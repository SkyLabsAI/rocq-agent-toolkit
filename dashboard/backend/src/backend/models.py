"""
Pydantic models for API request/response validation.
"""
from typing import Any

from pydantic import BaseModel, ConfigDict

# Wrtie now defining the Schema Directly
# Improt it from the Rocq pipeline schema later own.


class TokenCounts(BaseModel):
    """Token usage metrics."""

    input_tokens: int
    output_tokens: int
    total_tokens: int


class ResourceUsage(BaseModel):
    """Resource usage metrics."""

    execution_time_sec: float
    cpu_time_sec: float
    gpu_time_sec: float


class Metrics(BaseModel):
    """Task execution metrics."""

    llm_invocation_count: int
    token_counts: TokenCounts
    resource_usage: ResourceUsage
    custom: Any | None = None


class TaskMetadata(BaseModel):
    """Additional metadata for a task, including tags."""

    # Free-form tags attached to a task, e.g.
    tags: dict[str, str] = {}

    # Allow future metadata fields without breaking validation
    model_config = ConfigDict(extra="allow")


class TaskResult(BaseModel):
    """Complete task result entry from JSONL."""

    run_id: str
    task_kind: str
    task_id: str
    timestamp_utc: str
    agent_name: str
    status: str
    metrics: Metrics
    metadata: TaskMetadata = TaskMetadata()
    results: str | None = None
    failure_reason: list[str] | None = None


class RunInfo(BaseModel):
    """Summary information about a run, including derived metrics."""

    run_id: str
    agent_name: str
    timestamp_utc: str
    total_tasks: int
    success_count: int
    failure_count: int
    # Derived metrics
    success_rate: float = 0.0
    score: float = 0.0
    avg_total_tokens: float = 0.0
    avg_cpu_time_sec: float = 0.0
    metadata: TaskMetadata = TaskMetadata()


class AgentInfo(BaseModel):
    """Information about an agent plus its best-scoring run."""

    agent_name: str
    total_runs: int
    best_run: RunInfo | None = None


class RunDetailsResponse(BaseModel):
    """Response containing complete run details."""

    run_id: str
    agent_name: str
    total_tasks: int
    tasks: list[TaskResult]


class LogEntry(BaseModel):
    """Single log entry from Loki."""

    timestamp: str
    line: str
    labels: dict | None = None


class ObservabilityLogsResponse(BaseModel):
    """Response containing observability logs from Loki."""

    run_id: str
    task_id: str
    logs: list[LogEntry]
    total_logs: int


class RefreshResponse(BaseModel):
    """Response from refresh endpoint."""

    success: bool
    message: str
    total_tasks: int
    total_agents: int


class ObservabilityLabelsResponse(BaseModel):
    """Response containing unique labels from observability logs."""

    run_id: str
    task_id: str
    labels: dict[str, list[dict[str, Any]]] | None = None
    total_labels: int


class TagsResponse(BaseModel):
    """Response containing unique metadata tags across all tasks."""

    # Mapping from tag key to sorted list of unique values
    tags: dict[str, list[str]]
    total_keys: int
    total_values: int
