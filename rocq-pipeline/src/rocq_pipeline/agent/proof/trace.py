from typing import Any, override

from observability import get_logger
from rocq_doc_manager import RocqCursor

from rocq_pipeline.agent.base import (
    ProofAgent,
    TacticApplication,
    TaskResult,
)
from rocq_pipeline.proof_state import RocqGoal
from rocq_pipeline.schema.task_output import FailureReason

logger = get_logger("rocq_agent")


# NOTE: this agent does not support backtracking
#
# TODOS:
# - utilize structured proof tree
# - support (limited) backtracking
class TraceAgent(ProofAgent):
    def __init__(
        self,
        fuel: int | None = None,
        stop_on_failure: bool = False,
        goal_ty_upperbound: type[RocqGoal] = RocqGoal,
    ) -> None:
        super().__init__(goal_ty_upperbound=goal_ty_upperbound)
        self._max_fuel: int | None = fuel
        self._tac_app_cnt: int = 0
        self._stop_on_failure = stop_on_failure
        self._history: list[TacticApplication] = []

    async def next_tac(self, rdm: RocqCursor) -> str | TaskResult:
        """Get the next tactic string from the agent, or a TaskResult if the agent gives up."""
        return self.give_up(rdm, message="Not implemented")

    def history(self) -> list[TacticApplication]:
        """Get a shallow copy of the history."""
        return self._history[:]

    def last_failed(self) -> bool:
        """Check if the last tactic application failed."""
        if not self._history:
            return False

        return self._history[-1].err is not None

    def update_history(self, tac_app: TacticApplication) -> None:
        """Update the history with the new tactic application."""
        self._history.append(tac_app)

    @override
    async def prove(self, rdm: RocqCursor) -> TaskResult:
        """Keep trying to prove via next tactic prediction."""

        while True:
            pf_state_reply = self.current_proof_state(rdm)
            if isinstance(pf_state_reply, RocqCursor.Err):
                return self.give_up(
                    rdm,
                    message="{self.name()}: couldn't get current proof state",
                    reason=pf_state_reply,
                )
            elif pf_state_reply.closed(proof=True):
                break

            if self._max_fuel is not None and self._tac_app_cnt >= self._max_fuel:
                return self.give_up(
                    rdm,
                    message=f"{self.name()}: out of fuel after {self._tac_app_cnt} tactic applications",
                )
            elif self._stop_on_failure and self.last_failed():
                return self.give_up(
                    rdm,
                    message=f"{self.name()}: last tactic application failed after {self._tac_app_cnt} tactic applications",
                )

            # NOTE: overriders of `next` may emit additional logs
            # related to tactic prediction; we may want to create a (nested)
            # span here.
            next_tac_or_result: str | TaskResult = await self.next_tac(rdm)
            if isinstance(next_tac_or_result, TaskResult):
                return next_tac_or_result
            assert isinstance(next_tac_or_result, str)
            next_tac: str = next_tac_or_result
            if not next_tac.endswith("."):
                logger.warning(
                    f"{self.name()}: tactic sentence should end with a period"
                )
                next_tac += "."

            tac_app: TacticApplication = self.run_tactic(rdm, next_tac)
            self.update_history(tac_app)
            self._tac_app_cnt += 1

        return self.finished(rdm)

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
        return super().finished(
            rdm,
            message=message,
            side_effects=side_effects,
        )

    @override
    def give_up(
        self,
        rdm: RocqCursor,
        message: str = "",
        reason: FailureReason | RocqCursor.Err[Any] | BaseException | None = None,
        side_effects: dict[str, Any] | None = None,
    ) -> TaskResult:
        if side_effects is None:
            side_effects = {}
        self._extend_side_effects(rdm, side_effects)
        return super().give_up(
            rdm,
            message=message,
            reason=reason,
            side_effects=side_effects,
        )

    # NOTE: cf. similar note for _extend_side_effects + _task_doc_interaction
    # in ./strategy_agent.py

    def _extend_side_effects(
        self, rdm: RocqCursor, side_effects: dict[str, Any]
    ) -> None:
        assert side_effects is not None and isinstance(side_effects, dict)
        for k, v in {
            "doc_interaction": self._task_doc_interaction_json(rdm),
        }.items():
            if k in side_effects:
                logger.warning(f"overriding {k} with {v} in {side_effects}")
            side_effects[k] = v

    def _task_doc_interaction(self, rdm: RocqCursor) -> str:
        return "\n".join(
            [tac_app.tactic for tac_app in self.history() if tac_app.err is None]
        )

    def _task_doc_interaction_json(self, rdm: RocqCursor) -> Any:
        return self._task_doc_interaction(rdm)
