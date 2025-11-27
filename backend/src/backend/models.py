"""
Pydantic models for API request/response validation.
"""
import json
from typing import Any

from pydantic import BaseModel, ConfigDict, field_validator

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
    results: str | dict[str, Any] | None = None
    failure_reason: list[str] | None = None

    # TODO: remove this once the backend/frontend support `results`
    # being a dict (w/special handling for certain kinds of results)
    def model_post_init(self, __context__: Any = None) -> None:
        if isinstance(self.results, dict):
            pf_script = self.results.get("side_effects", {}).get("doc_interaction", "")
            self.results = pf_script

    @field_validator("results", mode="before")
    @classmethod
    def parse_results(cls, v: Any) -> str | dict[str, Any] | None:
        """
        Parse results field to handle both old (string) and new (dict) formats.

        If the value is a string, try to parse it as JSON. If parsing fails,
        return the string as-is for backward compatibility.
        If the value is already a dict, return it as-is.
        """
        if v is None:
            return None

        # If it's already a dict, return it
        if isinstance(v, dict):
            return v

        # If it's a string, try to parse as JSON
        if isinstance(v, str):
            try:
                parsed = json.loads(v)
                # If parsed to a dict, return it; otherwise return original string
                if isinstance(parsed, dict):
                    return parsed
                return v
            except (json.JSONDecodeError, TypeError):
                # If parsing fails, return the string as-is (backward compatibility)
                return v

        # For any other type, wrap in a dict or convert to string
        if isinstance(v, (list, int, float, bool)):
            # Wrap primitive types in a dict for consistency
            return {"value": v}

        # Fallback: return as string representation
        return str(v)


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
    avg_llm_invocation_count: float = 0.0
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
