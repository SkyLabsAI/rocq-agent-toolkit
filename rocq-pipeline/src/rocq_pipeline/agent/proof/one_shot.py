import logging
from typing import override

from rocq_doc_manager import RocqDocManager

from rocq_pipeline.agent.base import (
    AgentBuilder,
    Finished,
    GiveUp,
    ProofAgent,
    TacticApplication,
)
from rocq_pipeline.proof_state import RocqGoal
from rocq_pipeline.schema.task_output import ExecutionError, FailureReason

logger = logging.getLogger(__name__)


class OneShotAgent(ProofAgent):
    def __init__(
            self,
            tactic: str,
            goal_ty_upperbound: type[RocqGoal] = RocqGoal,
    ) -> None:
        super().__init__(goal_ty_upperbound=goal_ty_upperbound)
        if tactic.endswith("."):
            logger.warning(
                f"{self.name()}: tactic should not end with a period"
            )
        self._tactic: str = tactic.rstrip(".")
        self._tac_app: TacticApplication | None = None

    @property
    def tactic(self) -> str:
        return self._tactic

    @property
    def tactic_sentence(self) -> str:
        return f"{self._tactic}."

    @override
    def run(self, rdm: RocqDocManager) -> Finished | GiveUp:
        """Try to solve the goal in one shot using self._tactic."""
        self._tac_app = self.run_tactic(rdm, self.tactic_sentence)
        if self._tac_app.err:
            return self.give_up(
                rdm,
                reason=self._tac_app.err,
            )
        assert self._tac_app.pf_state_pre is not None
        assert self._tac_app.pf_state_post is not None

        if self._tac_app.pf_state_post.closed():
            return self.finished(rdm)
        else:
            return self.give_up(
                rdm,
                reason=FailureReason(ExecutionError(
                    f"tactic ({self._tactic}) failed to close the goal"
                ))
            )

    @override
    def task_doc_interaction(self, rdm_: RocqDocManager) -> str:
        if self._tac_app is not None and self._tac_app.err is None:
            return self.tactic_sentence
        else:
            return ""


class OneShotBuilder(AgentBuilder):
    def __init__(self) -> None:
        self._tactic: str | None = None

    def add_args(self, args: list[str]) -> None:
        if len(args) == 1:
            self._tactic = args[1]
        elif len(args) == 0:
            print("Missing tactic argument")
        else:
            print("Too many tactics given")

    @override
    def __call__(self, prompt: str | None = None) -> OneShotAgent:
        if self._tactic is None:
            print("Missing tactic argument")
            raise ValueError("Missing tactic argument")
        return OneShotAgent(self._tactic)
