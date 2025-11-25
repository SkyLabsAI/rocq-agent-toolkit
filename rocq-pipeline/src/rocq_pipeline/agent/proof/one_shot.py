import logging
from typing import override

from rocq_doc_manager import RocqDocManager

from rocq_pipeline.agent.base import AgentBuilder, Finished, GiveUp, ProofAgent
from rocq_pipeline.schema.task_output import ExecutionError, FailureReason

logger = logging.getLogger(__name__)


class OneShotAgent(ProofAgent):
    def __init__(self, tactic: str) -> None:
        if tactic.endswith("."):
            logger.warning(
                f"{self.name()}: tactic should not end with a period"
            )
        self._tactic: str = tactic.rstrip(".")
        self._solved: bool = False

    @override
    def run(self, rdm: RocqDocManager) -> Finished | GiveUp:
        """Try to solve the goal in one shot using self._tactic."""
        tac_app = self.run_tactic(rdm, f"{self._tactic}.")
        if tac_app.err:
            return self.give_up(
                rdm,
                reason=tac_app.err,
            )
        assert tac_app.pf_state_pre is not None
        assert tac_app.pf_state_post is not None

        if tac_app.pf_state_post.closed():
            self._solved = True
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
        if self._solved:
            return f"solve [{self._tactic}]."
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
