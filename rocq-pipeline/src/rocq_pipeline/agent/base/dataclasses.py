from dataclasses import dataclass, field
from typing import Any, Self

from rocq_doc_manager import RocqDocManager

from rocq_pipeline.proof_state import ProofState
from rocq_pipeline.schema import task_output

# TODO: improve how Rocq document interactions & partial progress
# are reflected in the [TaskResult]s.


@dataclass
class AgentConfig:
    """Base type for Rocq Agent Toolkit agent configurations."""
    pass


@dataclass
class TaskResult:
    """Base type for agent task results."""
    metrics: task_output.Metrics
    final_doc_interaction: Any
    final_holes: Any
    message: str


@dataclass
class GiveUp(TaskResult):
    """TaskResult: agent gave up, potentially after making some progress."""
    message: str = field(init=False)
    reason: task_output.FailureReason

    def __post_init__(self) -> None:
        self.message = f"failure: {str(self.reason)}"

    @classmethod
    def from_exception(
            cls,
            e: BaseException,
            metrics: task_output.Metrics | None = None,
            final_doc_interaction: Any = None,
            final_holes: Any = None,
    ) -> Self:
        if metrics is None:
            metrics = task_output.Metrics()
        return cls(
            metrics=metrics,
            final_doc_interaction=final_doc_interaction,
            final_holes=final_holes,
            reason=task_output.FailureReason(
                task_output.ExecutionError(str(e))
            )
        )


@dataclass
class Finished(TaskResult):
    """TaskResult: agent successfully completed the task."""
    message: str = "success"
    final_holes: Any = None


@dataclass
class TacticApplication:
    """Proof Tasks: [effect] of applying [tactic] in [proof_state]."""
    tactic: str
    pf_state_pre: ProofState | None = None
    pf_state_post: ProofState | None = None
    err: RocqDocManager.Err | None = None
