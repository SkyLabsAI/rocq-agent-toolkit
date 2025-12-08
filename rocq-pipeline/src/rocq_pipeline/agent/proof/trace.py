from typing import Any, override

from observability import get_logger
from rocq_doc_manager import RocqDocManager

from rocq_pipeline.agent.base import (
    ProofAgent,
    TacticApplication,
    TaskResult,
)
from rocq_pipeline.proof_state import ProofState, RocqGoal
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

    def next_tac(self, rdm: RocqDocManager) -> str | TaskResult:
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
    def prove(self, rdm: RocqDocManager) -> TaskResult:
        """Keep trying to prove via next tactic prediction."""
        while not self.current_proof_state(rdm).closed(proof=True):
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
            next_tac_or_result: str | TaskResult = self.next_tac(rdm)
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
            rdm: RocqDocManager,
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
            rdm: RocqDocManager,
            message: str = "",
            reason: FailureReason | RocqDocManager.Err[Any] | BaseException | None = None,
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

    def _extend_side_effects(
            self,
            rdm: RocqDocManager,
            side_effects: dict[str, Any]
    ) -> None:
        assert side_effects is not None and isinstance(side_effects, dict)
        for k, v in {
            "doc_interaction": self._task_doc_interaction_json(rdm),
            "holes": self._task_holes_json(rdm)
        }.items():
            if k in side_effects:
                logger.warning(
                    f"overriding {k} with {v} in {side_effects}"
                )
            side_effects[k] = v

    # NOTE: _task_holes + _task_doc_interaction are used to report
    # information about the state of the document when the task
    # concludes, via `side_effects`

    def _task_holes(
        self,
        rdm: RocqDocManager,
    ) -> ProofState | RocqDocManager.Err[Any]:
        current_goal_reply = rdm.current_goal()
        if isinstance(current_goal_reply, RocqDocManager.Err):
            return current_goal_reply
        return ProofState(
            current_goal_reply,
            goal_ty_upperbound=self._goal_ty_upperbound,
        )

    def _task_holes_json(self, rdm: RocqDocManager) -> dict[str, Any] | str:
        holes = self._task_holes(rdm)
        if isinstance(holes, RocqDocManager.Err):
            return str(holes)
        else:
            return holes.to_json()

    def _task_doc_interaction(self, rdm: RocqDocManager) -> str:
        return "\n".join(
            [tac_app.tactic for tac_app in self._history if not tac_app.err]
        )

    def _task_doc_interaction_json(self, rdm: RocqDocManager) -> Any:
        return self._task_doc_interaction(rdm)
