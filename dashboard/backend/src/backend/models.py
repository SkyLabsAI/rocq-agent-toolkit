"""
Pydantic models for API request/response validation.
"""

import json
from typing import Any

from pydantic import BaseModel, ConfigDict, Field, field_validator

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
    # For ingestion: task_id is the logical string identifier
    # For API responses: task_id is the database integer ID, task_name is the logical string
    task_id: int | str  # int when returned from API, str when ingested from JSONL
    task_name: str | None = (
        None  # Logical task identifier (e.g., "ArrayCopy.v#lemma:test_ok")
    )
    trace_id: str | None = (
        None  # None for backward compatibility with older ingestions.
    )
    dataset_id: str | None = (
        None  # Can be None for backward compatibility with older ingestions.
    )
    ground_truth: str | None = None
    timestamp_utc: str
    agent_cls_checksum: str
    agent_checksum: str
    status: str
    metrics: Metrics
    metadata: TaskMetadata = TaskMetadata()
    # Results can be an arbitrary JSON structure or a plain string.
    results: str | dict[str, Any] | None = None
    failure_reason: list[str] | None = None

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
        # It may be a JSON String with the results of the task
        if isinstance(v, str):
            try:
                parsed = json.loads(v)
                # If parsed to a dict, return it; otherwise return original string
                if isinstance(parsed, dict):
                    return parsed
            except (json.JSONDecodeError, TypeError):
                # If parsing fails, return the string as a JSON (backward compatibility)
                return {"side_effects": {"doc_interaction": v}}

        return {
            "side_effects": {"doc_interaction": v}
        }  # fallback to the JSON-Dict [str:Any] format


class RunInfo(BaseModel):
    """Summary information about a run, including derived metrics."""

    run_id: str
    agent_cls_checksum: str
    agent_checksum: str
    timestamp_utc: str
    dataset_id: str | None = None
    total_tasks: int
    success_count: int
    failure_count: int
    # Derived metrics
    success_rate: float = 0.0
    score: float = 0.0  # Dynamically Computed based on the compute_Score function
    avg_total_tokens: float = 0.0
    avg_llm_invocation_count: float = 0.0
    avg_cpu_time_sec: float = 0.0
    best_run: bool = False
    metadata: TaskMetadata = TaskMetadata()


class AgentClassProvenance(BaseModel):
    """Agent class provenance data."""

    cls_checksum: str
    cls_name: str
    cls_provenance: dict[str, Any]


class AgentInstanceProvenance(BaseModel):
    """Agent instance provenance data."""

    agent_checksum: str
    cls_checksum: str
    name: str
    provenance: dict[str, Any]


class AgentInstanceSummary(BaseModel):
    """Information about an agent instance plus its best-scoring run.

    Similar to AgentClassSummary but for individual instances.
    """

    agent_checksum: str
    cls_checksum: str
    name: str
    provenance: dict[str, Any]
    total_runs: int
    best_run: RunInfo | None = None


class AgentClassSummary(BaseModel):
    """Information about an agent class plus its best-scoring run.

    Replaces AgentInfo - combines provenance data with aggregate stats.
    """

    cls_checksum: str
    cls_name: str
    cls_provenance: dict[str, Any]
    total_runs: int
    best_run: RunInfo | None = None


class RunDetailsResponse(BaseModel):
    """Response containing complete run details."""

    run_id: str
    agent_cls_checksum: str
    agent_checksum: str
    total_tasks: int
    tasks: list[TaskResult]


class LogEntry(BaseModel):
    """Single log entry from Loki."""

    timestamp: str
    line: str
    labels: dict[str, Any]


class ObservabilityLogsResponse(BaseModel):
    """Response containing observability logs from Loki."""

    run_id: str
    task_id: int
    task_name: str
    logs: list[LogEntry]
    total_logs: int


class GraphNode(BaseModel):
    """Graph node for observability-derived cursor graphs."""

    id: str
    index: int
    information: dict[str, Any] = Field(default_factory=dict)


class GraphEdge(BaseModel):
    """Graph edge for observability-derived cursor graphs."""

    source: str
    target: str
    label: str
    index: int
    information: dict[str, Any] = Field(default_factory=dict)


class GraphData(BaseModel):
    """Graph payload containing nodes and edges."""

    nodes: list[GraphNode]
    edges: list[GraphEdge]
    information: dict[str, Any] = Field(default_factory=dict)


class ObservabilityGraphResponse(BaseModel):
    """Response containing a graph built from observability logs."""

    run_id: str
    task_id: int
    task_name: str
    graph: GraphData
    total_nodes: int
    total_edges: int


class RefreshResponse(BaseModel):
    """Response from refresh endpoint."""

    success: bool
    message: str
    total_tasks: int
    total_agents: int


class ObservabilityLabelsResponse(BaseModel):
    """Response containing unique labels from observability logs."""

    run_id: str
    task_id: int
    task_name: str
    labels: dict[str, list[dict[str, Any]]] | None = None
    total_labels: int


class TagsResponse(BaseModel):
    """Response containing unique metadata tags across all tasks."""

    # Mapping from tag key to sorted list of unique values
    tags: dict[str, list[str]]
    total_keys: int
    total_values: int


class IngestionResponse(BaseModel):
    """Response returned by the JSONL ingestion endpoint."""

    success: bool
    message: str
    runs_ingested: int
    tasks_ingested: int


class TaskDatasetIngestionResponse(BaseModel):
    """Response returned by the YAML task dataset ingestion endpoint."""

    success: bool
    message: str
    dataset_id: str
    tasks_created: int
    tasks_updated: int


class DatasetInfo(BaseModel):
    """Summary information about a dataset."""

    dataset_id: str
    description: str | None = None
    created_at: str | None = None


class BestRunUpdateResponse(BaseModel):
    """Response for endpoints that toggle the best_run flag on a run."""

    run_id: str
    best_run: bool


class VisualizerTraceIdsResponse(BaseModel):
    """Trace IDs associated with a run (derived from Loki logs)."""

    run_id: str
    trace_ids: list[str]
    total: int


class VisualizerSpanLite(BaseModel):
    """Parsed span record (best-effort) for visualizer use."""

    trace_id: str
    span_id: str
    parent_span_id: str | None = None
    name: str
    service_name: str
    status: dict[str, Any] | None = None  # status code and message
    start_time_unix_nano: str | None = None
    end_time_unix_nano: str | None = None
    attributes: dict[str, Any] = {}
    events: list[dict[str, Any]] = []  # span events with timestamps and attributes
    links: list[dict[str, Any]] = []  # links to other traces/spans


class VisualizerSpansResponse(BaseModel):
    spans: list[VisualizerSpanLite]


# ============================================================================
# Dataset Tasks API Response Models
# ============================================================================


class TaskInfo(BaseModel):
    """Information about a task in a dataset."""

    task_id: int  # Database primary key
    task_name: str  # Logical task identifier (e.g., "ArrayCopy.v#lemma:test_ok")
    task_kind: str | None = None
    dataset_id: str | None = None
    tags: dict[str, str] = {}  # Task-level tags (extracted from TASK_ prefixed tags)


class TaskDetailsResponse(BaseModel):
    """Complete task details for a single task (no run results)."""

    task_id: int  # Database primary key
    task_name: str  # Logical task identifier (e.g., "ArrayCopy.v#lemma:test_ok")
    task_kind: str | None = None
    dataset_id: str | None = None
    dataset: DatasetInfo | None = None
    ground_truth: str | None = None
    tags: dict[str, str] = {}  # Task-level tags (extracted from TASK_ prefixed tags)


class DatasetTasksResponse(BaseModel):
    """Response containing all tasks in a dataset."""

    dataset_id: str
    tasks: list[TaskInfo]
    total_tasks: int


class DatasetResultsTask(BaseModel):
    """Task information for the dataset results matrix."""

    task_id: int  # Database primary key
    task_name: str  # Logical task identifier
    task_kind: str | None = None
    dataset_id: str | None = None
    tags: dict[str, str] = {}


class DatasetResultsAgentInstance(BaseModel):
    """Agent instance information for the dataset results matrix."""

    agent_instance_id: str  # agent_checksum (same as agent_checksum for clarity)
    agent_name: str
    agent_checksum: str
    agent_cls_checksum: str
    agent_cls_name: str
    provenance: dict[str, Any] = {}
    run_ids: list[str] = []


class DatasetTaskResult(BaseModel):
    """Individual result in the dataset results matrix.

    Represents the aggregated success/failure counts for a specific
    task and agent instance combination across all runs.
    """

    task_id: int  # References a task from tasks array
    agent_instance_id: str  # References an agent instance (agent_checksum)
    success_count: int
    total_count: int


class DatasetResultsResponse(BaseModel):
    """Response containing the complete results matrix for a dataset.

    This is the main API response for the dataset details page,
    showing task results across all agent instances.
    """

    dataset_id: str
    tasks: list[DatasetResultsTask]
    agent_instances: list[DatasetResultsAgentInstance]
    results: list[DatasetTaskResult]


class BulkAddTagsRequest(BaseModel):
    """Request to add tags to multiple tasks."""

    task_ids: list[int]  # List of task database IDs
    tags: list[str]  # Tags to add (each string is used as both key and value)


class BulkAddTagsResponse(BaseModel):
    """Response from bulk tag addition."""

    success: bool
    message: str
    tasks_updated: int
    tags_added: int


class AgentTaskRunsResponse(BaseModel):
    """Response containing all run IDs for an agent instance on a specific task."""

    agent_checksum: str
    task_id: int
    task_name: str
    run_ids: list[str]
    total_runs: int
