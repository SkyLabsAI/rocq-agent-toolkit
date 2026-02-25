from dataclasses import dataclass, field
from typing import Any, Self

from observability import get_logger
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

from rocq_pipeline.proof_state import ProofState
from rocq_pipeline.schema import task_output

logger = get_logger("rocq_agent")


@dataclass
class AgentConfig:
    """Base type for Rocq Agent Toolkit agent configurations."""


@dataclass
class TaskResult:
    """Base type for agent results on any task."""

    message: str = field(kw_only=True)
    failure_reason: task_output.FailureReason | None = field(kw_only=True, default=None)
    side_effects: dict[str, Any] = field(kw_only=True, default_factory=dict)
    # TODO: remove `_metrics` once opentelemetry instrumentation is in place
    _metrics: task_output.Metrics = field(
        kw_only=True,
        default_factory=task_output.Metrics,
    )

    @property
    def success(self) -> bool:
        """Whether the task was successful."""
        return self.failure_reason is None

    @property
    def exception(self) -> bool:
        """Whether the task concluded in an error."""
        return self.failure_reason is not None and isinstance(
            self.failure_reason.value, task_output.ExecutionError
        )

    @classmethod
    def finished(
        cls,
        message: str,
        side_effects: dict[str, Any] | None = None,
        _metrics: task_output.Metrics | None = None,
    ) -> Self:
        """Create a TaskResult when the agent finishes successfully."""
        return cls(
            message=message,
            failure_reason=None,
            side_effects=side_effects or {},
            _metrics=task_output.Metrics() if _metrics is None else _metrics,
        )

    @classmethod
    def give_up(
        cls,
        message: str,
        reason: rdm_api.Err[Any] | task_output.FailureReason | None = None,
        side_effects: dict[str, Any] | None = None,
        _metrics: task_output.Metrics | None = None,
    ) -> Self:
        """Create a TaskResult when the agent gives up."""
        if isinstance(reason, rdm_api.Err):
            failure_reason = task_output.FailureReason(
                task_output.ExecutionError(str(reason))
            )
        else:
            failure_reason = (
                reason
                if reason is not None
                else task_output.FailureReason(task_output.Other(message))
            )
        return cls(
            message=message,
            failure_reason=failure_reason,
            side_effects=side_effects or {},
            _metrics=task_output.Metrics() if _metrics is None else _metrics,
        )

    @classmethod
    def from_exception(
        cls,
        e: BaseException,
        message: str | None = None,
        side_effects: dict[str, Any] | None = None,
        _metrics: task_output.Metrics | None = None,
    ) -> Self:
        """Create a TaskResult from an exception."""
        if not message:
            message = repr(e)
        return cls.give_up(
            message=message,
            reason=task_output.FailureReason(task_output.ExecutionError(repr(e))),
            side_effects=side_effects or {},
            _metrics=task_output.Metrics() if _metrics is None else _metrics,
        )

    def to_task_output(
        self,
        *,
        agent_cls_checksum: str,
        agent_checksum: str,
        run_id: str | None = None,
        task_kind: task_output.TaskKind | None = None,
        task_id: str | None = None,
        dataset_id: str | None = None,
        timestamp_utc: str | None = None,
        trace_id: str | None = None,
        metadata: task_output.Metadata | None = None,
    ) -> task_output.TaskOutput:
        """Convert this TaskResult to a task_output.TaskOutput.

        This method is used by task_runner.py to construct the final TaskOutput.
        Subclasses should override this to provide task-specific data.

        Returns:
            A new TaskOutput with this result's status, metrics, and other data.
        """
        if self.success:
            status = task_output.TaskStatus(task_output.Success())
        else:
            status = task_output.TaskStatus(task_output.Failure())

        if (
            run_id is None
            or task_kind is None
            or task_id is None
            or dataset_id is None
            or timestamp_utc is None
        ):
            missing = [
                k
                for k, v in {
                    "run_id": run_id,
                    "task_kind": task_kind,
                    "task_id": task_id,
                    "timestamp_utc": timestamp_utc,
                }.items()
                if v is None
            ]
            raise ValueError(f"Missing required fields: {', '.join(missing)}")

        return task_output.TaskOutput(
            run_id=run_id,
            task_kind=task_kind,
            task_id=task_id,
            dataset_id=dataset_id,
            trace_id=trace_id,
            timestamp_utc=timestamp_utc,
            agent_cls_checksum=agent_cls_checksum,
            agent_checksum=agent_checksum,
            status=status,
            # TODO: remove `self.metrics` once opentelemetry instrumentation is in place
            metrics=self._metrics,
            failure_reason=self.failure_reason,
            results={
                "message": self.message,
                "side_effects": self.side_effects,
            },
            metadata=metadata,
        )


@dataclass
class TacticApplication:
    """Proof Tasks: [effect] of applying [tactic] in [proof_state]."""

    tactic: str
    pf_state_pre: ProofState | None = None
    pf_state_post: ProofState | None = None
    err: rdm_api.Err | None = None
