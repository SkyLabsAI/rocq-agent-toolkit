import itertools
from dataclasses import dataclass
from typing import override

from observability import trace_context
from rocq_doc_manager import RocqCursor

from rocq_pipeline.agent import (
    TaskResult,
)
from rocq_pipeline.agent.base import ProofAgent
from rocq_pipeline.proof_state import ProofState, RocqGoal
from rocq_pipeline.search.action import Action
from rocq_pipeline.search.strategy import Strategy


class StrategyAgent(ProofAgent, VERSION="0.1.0"):
    """An agent that uses a Strategy to select tactics."""

    def __init__(
        self,
        strategy: Strategy,
        max_depth: int | None = None,
        max_breath: int | None = None,
        fuel: int | None = None,
    ) -> None:
        super().__init__(goal_ty_upperbound=RocqGoal)
        self._strategy = strategy
        self._max_depth = max_depth
        self._max_breath = max_breath
        self._fuel = fuel

    def prepare(self, rc: RocqCursor) -> None:
        pass

    @dataclass
    class NoProofState(Exception):
        reason: RocqCursor.Err

    def _current_state(self, rc: RocqCursor) -> ProofState:
        reply = rc.current_goal()
        if isinstance(reply, RocqCursor.Err):
            raise StrategyAgent.NoProofState(reply)
        return ProofState(reply)

    @override
    def prove(self, rc: RocqCursor) -> TaskResult:
        self.prepare(rc)

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

                rollout = self._strategy.rollout(rc)
                for _, action in (
                    rollout
                    if self._max_breath is None
                    else itertools.islice(rollout, self._max_breath)
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
                        rc, f"No more proposals (max_breath={self._max_breath}"
                    )
