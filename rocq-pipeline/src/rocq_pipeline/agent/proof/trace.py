from abc import abstractmethod
from typing import override

from observability import get_logger
from rocq_doc_manager import RocqDocManager

from rocq_pipeline.agent.base import (
    Finished,
    GiveUp,
    ProofAgent,
    TacticApplication,
)
from rocq_pipeline.proof_state import RocqGoal
from rocq_pipeline.schema.task_output import ExecutionError, FailureReason

logger = get_logger("rocq_agent")


# NOTE: this agent does not support backtracking
#
# TODOS:
# - utilize structured proof tree
# - support (limited) backtracking
class TraceAgent(ProofAgent):
    def __init__(
            self,
            stop_on_failure: bool = False,
            goal_ty_upperbound: type[RocqGoal] = RocqGoal,
    ) -> None:
        super().__init__(goal_ty_upperbound=goal_ty_upperbound)
        self._stop_on_failure = stop_on_failure
        self._history: list[TacticApplication] = []

    @abstractmethod
    def next_tac(self, rdm: RocqDocManager) -> str | GiveUp:
        """Get the next tactic string."""
        ...

    @override
    def run(self, rdm: RocqDocManager) -> Finished | GiveUp:
        # Start trying to verify the code
        #
        # TODO: add fuel to guard against agents that never give up
        # and never succeed.
        while not self.task_finished(rdm):
            if self._stop_on_failure and self.last_failed():
                return self.give_up(
                    rdm,
                    reason=FailureReason(ExecutionError("Tactic failure.")),
                )

            # NOTE: overriders of `next` may emit additional logs
            # related to tactic prediction; we may want to create a (nested)
            # span here.
            next_tac_or_give_up = self.next_tac(rdm)
            if isinstance(next_tac_or_give_up, GiveUp):
                return next_tac_or_give_up
            next_tac: str = next_tac_or_give_up
            if not next_tac.endswith("."):
                logger.warning(
                    f"{self.name()}: tactic sentence should end with a period"
                )
                next_tac += "."

            tac_app: TacticApplication = self.run_tactic(rdm, next_tac)
            self.update_history(tac_app)

        return self.finished(rdm)

    @override
    def task_doc_interaction(self, rdm_: RocqDocManager) -> str:
        return "\n".join([
            tac_app.tactic
            for tac_app in self._history
            if not tac_app.err
        ])

    def last_failed(self) -> bool:
        if not self._history:
            return False

        return self._history[-1].err is not None

    def update_history(self, tac_app: TacticApplication) -> None:
        self._history.append(tac_app)

    def history(self) -> list[TacticApplication]:
        # Note: return a shallow copy of the history
        return self._history[:]
