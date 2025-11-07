"""
Pydantic models for API request/response validation.
"""
from typing import Optional, Any, List
from pydantic import BaseModel

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
    custom: Optional[Any] = None


class TaskResult(BaseModel):
    """Complete task result entry from JSONL."""

    run_id: str
    task_kind: str
    task_id: str
    timestamp_utc: str
    agent_name: str
    status: str
    metrics: Metrics
    results: Optional[str] = None
    failure_reason: Optional[List[str]] = None


class AgentInfo(BaseModel):
    """Information about an agent."""

    agent_name: str
    total_runs: int


class RunInfo(BaseModel):
    """Summary information about a run."""

    run_id: str
    agent_name: str
    timestamp_utc: str
    total_tasks: int
    success_count: int
    failure_count: int


class RunDetailsResponse(BaseModel):
    """Response containing complete run details."""

    run_id: str
    agent_name: str
    total_tasks: int
    tasks: List[TaskResult]


class LogEntry(BaseModel):
    """Single log entry from Loki."""

    timestamp: str
    line: str
    labels: Optional[dict] = None


class ObservabilityLogsResponse(BaseModel):
    """Response containing observability logs from Loki."""

    run_id: str
    task_id: str
    logs: List[LogEntry]
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
    labels: Optional[dict] = None
    total_labels: int
