import logging
from typing import Annotated, override

from provenance_toolkit import Provenance
from rocq_doc_manager import RocqCursor

from rocq_pipeline.agent.base import (
    AgentBuilder,
    TaskResult,
)
from rocq_pipeline.proof_state import RocqGoal

from .trace import TraceAgent

logger = logging.getLogger(__name__)


class OneShotAgent(TraceAgent, VERSION="1.0.0"):
    """OneShotAgent: Derives from TraceAgent with a restriction on tactic applications (max 1)."""

    _tactic: Annotated[str, Provenance.Reflect.Field]

    def __init__(
        self,
        tactic: str,
        goal_ty_upperbound: type[RocqGoal] = RocqGoal,
    ) -> None:
        super().__init__(
            goal_ty_upperbound=goal_ty_upperbound,
            fuel=1,
        )
        if tactic.endswith("."):
            logger.warning(f"{self.name()}: tactic should not end with a period")
        self._tactic: str = tactic.rstrip(".")

    @property
    def tactic(self) -> str:
        return self._tactic

    @property
    def tactic_sentence(self) -> str:
        return f"{self._tactic}."

    @override
    def next_tac(self, rdm: RocqCursor) -> str | TaskResult:
        """Get the next tactic string, but only allow one application."""
        return self.tactic_sentence


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
