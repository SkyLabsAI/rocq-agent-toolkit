from __future__ import annotations

import itertools
from dataclasses import dataclass
from types import MappingProxyType
from typing import Annotated, Any, override

from observability import get_logger, trace_context
from provenance_toolkit import Provenance
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

from rocq_pipeline.agent.base import ProofAgent
from rocq_pipeline.agent.base.dataclasses import TaskResult
from rocq_pipeline.proof_state import ProofState, RocqGoal
from rocq_pipeline.schema.task_output import FailureReason
from rocq_pipeline.search.action import Action
from rocq_pipeline.search.strategy import Strategy

logger = get_logger("rocq_agent")


class StrategyAgent(ProofAgent):
    """An agent that uses a Strategy to select tactics."""

    _strategy: Annotated[Strategy, Provenance.Reflect.Field]
    _max_depth: Annotated[int | None, Provenance.Reflect.Field]
    _max_breath: Annotated[int | None, Provenance.Reflect.Field]
    _fuel: Annotated[int | None, Provenance.Reflect.Field]

    def __init__(
        self,
        strategy: Strategy,
        max_depth: int | None = None,
        max_breadth: int | None = None,
        fuel: int | None = None,
    ) -> None:
        super().__init__(goal_ty_upperbound=RocqGoal)
        self._strategy = strategy
        self._max_depth = max_depth
        self._max_breadth = max_breadth
        self._fuel = fuel
        self._initial_prove_cursor_index: int | None = None

    def prepare(self, rc: RocqCursor) -> Strategy.MutableContext:
        """Pre-hook for prove."""
        self._initial_prove_cursor_index = rc.cursor_index()
        rc.insert_command("Unset SsrIdents.")
        return {}

    def conclude(self, rc: RocqCursor) -> None:
        """Post-hook for prove -- transitively, via finished/give_up."""
        self._initial_prove_cursor_index = None

    @dataclass
    class NoProofState(Exception):
        reason: rdm_api.Err

    def _current_state(self, rc: RocqCursor) -> ProofState:
        reply = rc.current_goal()
        if isinstance(reply, rdm_api.Err):
            raise StrategyAgent.NoProofState(reply)
        return ProofState(reply)

    @override
    async def prove(self, rc: RocqCursor) -> TaskResult:
        # Note: `prepare` uses `Strategy.MutableContext` so derivers can incrementalize
        # construction via super().prepare calls, but prove/rollout promises to leave
        # it unchanged.
        strategy_ctx: Strategy.Context = MappingProxyType(self.prepare(rc))

        fresh_id: int = 0

        def fresh() -> int:
            nonlocal fresh_id
            t = fresh_id
            fresh_id += 1
            return t

        current_id = fresh()
        with trace_context("strategy_agent") as span:
            span.set_attribute("root_id", current_id)

            depth: int = 0
            rem_fuel: int | None = self._fuel
            while True:
                state = self._current_state(rc)
                if state.closed(proof=True):
                    return self.finished(rc)

                if self._max_depth is not None and depth >= self._max_depth:
                    return self.give_up(
                        rc,
                        message=f"depth limit exceeded({self._max_depth})",
                    )

                rollout = self._strategy.rollout(
                    rc, max_rollout=self._max_breadth, context=strategy_ctx
                )
                for _, action in (
                    rollout
                    if self._max_breadth is None
                    else itertools.islice(rollout, self._max_breadth)
                ):
                    if rem_fuel is not None:
                        rem_fuel -= 1
                        if rem_fuel <= 0:
                            return self.give_up(
                                rc, message=f"out of fuel ({self._fuel})"
                            )
                    with trace_context("strategy_agent/process") as process:
                        process.set_attribute("parent", current_id)
                        process.set_attribute("action", action.key())
                        action_rc = rc.clone()
                        try:
                            rc = action.interact(action_rc)
                            if rc is not action_rc:
                                action_rc.dispose()
                            current_id = fresh()
                            process.set_attribute("id", current_id)
                            depth += 1
                            break
                        except Action.Failed:
                            action_rc.dispose()
                else:
                    # not executed if we see a break
                    return self.give_up(
                        rc, f"No more proposals (max_breadth={self._max_breadth})"
                    )

    @override
    def finished(
        self,
        rdm: RocqCursor,
        message: str = "",
        side_effects: dict[str, Any] | None = None,
    ) -> TaskResult:
        if side_effects is None:
            side_effects = {}
        self._extend_side_effects(rdm, side_effects)
        result = super().finished(
            rdm,
            message=message,
            side_effects=side_effects,
        )
        self.conclude(rdm)
        return result

    @override
    def give_up(
        self,
        rdm: RocqCursor,
        message: str = "",
        reason: FailureReason | rdm_api.Err[Any] | BaseException | None = None,
        side_effects: dict[str, Any] | None = None,
    ) -> TaskResult:
        if side_effects is None:
            side_effects = {}
        self._extend_side_effects(rdm, side_effects)
        result = super().give_up(
            rdm,
            message=message,
            reason=reason,
            side_effects=side_effects,
        )
        self.conclude(rdm)
        return result

    # NOTE:
    # - _extend_side_effects uses _task_doc_interaction to report information
    #   about the state of the document when the task concludes, via `side_effects`.
    #   + This works well enough for StrategyAgent since there is no (parallel)
    #     exploration and no interesting traversal over (decomposed) goals; the final
    #     `rc` we supply will always be the "furthest" through the proof.
    #   + This may work less well for SearchAgent due to parallel exploration;
    #     we'd need a cursor that captures the "final" document state, but we may
    #     not have one readily accessible.
    # - We're going to use telemetry to reconstruct the document interaction(s)
    #   in a proof-state / action visualizer for the dashboard. We should plan to
    #   leverage this in order to compute doc-interaction strings on demand, which
    #   enables us to capture both the "final" and "intermediate" proof scripts.

    def _extend_side_effects(
        self, rc: RocqCursor, side_effects: dict[str, Any]
    ) -> None:
        assert side_effects is not None and isinstance(side_effects, dict)
        for k, v in {
            "doc_interaction": self._task_doc_interaction_json(rc),
        }.items():
            if k in side_effects:
                logger.warning(f"overriding {k} with {v} in {side_effects}")
            side_effects[k] = v

    def _task_doc_interaction(self, rc: RocqCursor) -> str:
        assert self._initial_prove_cursor_index is not None
        return "".join(
            prefix_item.text
            for prefix_item in rc.doc_prefix()[self._initial_prove_cursor_index :]
        )

    def _task_doc_interaction_json(self, rc: RocqCursor) -> Any:
        return self._task_doc_interaction(rc)
