"""
SQLModel database models for the RAT Dashboard.
These models map directly to PostgreSQL tables.
"""

from datetime import UTC, datetime
from typing import Any
from uuid import UUID

from sqlalchemy import JSON, Column, Integer
from sqlmodel import Field, Relationship, SQLModel


class AgentClassProvenance(SQLModel, table=True):
    """Agent class provenance model - stores provenance data for agent classes.

    Class-level runs are derived by aggregating all instance runs where
    AgentProvenance.cls_checksum matches this cls_checksum.
    """

    __tablename__ = "agent_class_provenance"

    cls_checksum: str = Field(primary_key=True, index=True)
    cls_name: str
    cls_provenance: dict[str, Any] = Field(sa_column=Column(JSON))
    first_seen: datetime = Field(default_factory=lambda: datetime.now(UTC))

    # Relationships
    instances: list["AgentProvenance"] = Relationship(back_populates="agent_class")
    runs: list["Run"] = Relationship(back_populates="agent_class")


# Notes re data model:
# - Corresponds to "Agent"
# - Logged during `TaskResult` construction in `rocq-pipeline`
# - Ingested when `TaskResult` is uploaded
# - Re tags:
#   + some tags may be captured by the `provenance`
#   + separate agent tags are not crucial in the short term but may become
#     more useful in the future (e.g. "best_agent" tag)
# - Primary key: `agent_checksum`, stably computed via `provenance`
class AgentProvenance(SQLModel, table=True):
    """Agent instance provenance model - stores provenance data for agent instances."""

    __tablename__ = "agent_provenance"

    agent_checksum: str = Field(primary_key=True, index=True)
    cls_checksum: str = Field(
        foreign_key="agent_class_provenance.cls_checksum", index=True
    )
    name: str
    provenance: dict[str, Any] = Field(sa_column=Column(JSON))
    first_seen: datetime = Field(default_factory=lambda: datetime.now(UTC))

    # Relationships
    agent_class: AgentClassProvenance = Relationship()
    runs: list["Run"] = Relationship(back_populates="agent_instance")


# Notes re data model:
# - Corresponds to "Project", so we should rename this
class Dataset(SQLModel, table=True):
    """Dataset model - represents a collection of tasks."""

    __tablename__ = "dataset"

    # Auto-generated surrogate key; the logical identifier from JSONL
    # (e.g. "loop_corpus") is stored in the `name` column.
    # We make the auto-increment behaviour explicit at the SQLAlchemy level.
    id: int | None = Field(
        default=None,
        sa_column=Column(Integer, primary_key=True, autoincrement=True),
    )
    name: str = Field(unique=True, index=True)
    description: str | None = None
    created_at: datetime | None = Field(default_factory=lambda: datetime.now(UTC))

    # Relationships
    tasks: list["Task"] = Relationship(back_populates="dataset")
    runs: list["Run"] = Relationship(back_populates="dataset")


# Notes re data model:
# - Primary key:
#   + tasks are only unique relative to project
#     ==> project ID must be part of task ID
#   + Using an auto-increment primary key with separate indices for efficient
#     lookups based on project ID + task locator
# - Tags:
#   + Task tags are extracted from `TaskResult` (with "TASK_" prefix)
#   + Many-to-many relationship via TaskTagLink
#   + Ability to modify task tags post facto (e.g. by tagging tasks with a date)
class Task(SQLModel, table=True):
    """Task model - represents a problem/task being solved."""

    __tablename__ = "task"

    # Auto-generated surrogate key; the logical identifier from JSONL
    # (e.g. "ArrayCopy.v#lemma:test_ok") is stored in the `name` column.
    id: int | None = Field(
        default=None,
        sa_column=Column(Integer, primary_key=True, autoincrement=True),
    )
    # The logical task identifier (e.g., "ArrayCopy.v#lemma:test_ok")
    name: str = Field(index=True)
    kind: str | None = None
    # Foreign key to Dataset; nullable for backward compatibility with
    # older ingested data that did not include dataset information.
    dataset_id: int | None = Field(foreign_key="dataset.id", index=True)
    difficulty_score: int = Field(default=0)

    # Relationships
    results: list["TaskResultDB"] = Relationship(back_populates="task")
    dataset: Dataset = Relationship(back_populates="tasks")
    tag_links: list["TaskTagLink"] = Relationship(back_populates="task")

    # Note: The combination of (name, dataset_id) should be unique.
    # This is enforced at the application level during ingestion.


class Tag(SQLModel, table=True):
    """Tag model - metadata key-value pairs."""

    __tablename__ = "tag"

    id: int | None = Field(default=None, primary_key=True)
    key: str = Field(index=True)
    value: str

    # Relationships
    run_links: list["RunTagLink"] = Relationship(back_populates="tag")
    task_links: list["TaskTagLink"] = Relationship(back_populates="tag")


class RunTagLink(SQLModel, table=True):
    """Link table for many-to-many relationship between runs and tags."""

    __tablename__ = "run_tag_link"

    run_id: UUID = Field(foreign_key="run.id", primary_key=True)
    tag_id: int = Field(foreign_key="tag.id", primary_key=True)

    # Relationships
    run: "Run" = Relationship(back_populates="tag_links")
    tag: Tag = Relationship(back_populates="run_links")


class TaskTagLink(SQLModel, table=True):
    """Link table for many-to-many relationship between tasks and tags.

    Task tags are extracted from metadata tags with the "TASK_" prefix during
    ingestion. The prefix is stripped when storing the tag key.
    """

    __tablename__ = "task_tag_link"

    task_id: int = Field(foreign_key="task.id", primary_key=True)
    tag_id: int = Field(foreign_key="tag.id", primary_key=True)

    # Relationships
    task: "Task" = Relationship(back_populates="tag_links")
    tag: Tag = Relationship(back_populates="task_links")


# Notes re data model:
# - this seemed mostly OK
# - `is_best_run` can probably dropped
# - Q: how important is run concept/visualization for users?
#   + Gregory: this will be useful for debugging / optimizing our pipeline exeuction
#     framework, but it is probably less important for agent development
#   + Ehtesham/Jasper: once the data provenance changes get merged `Run` will be less
#     important for the frontend
# - metadata will likely be stripped from this part of the DB schema since we can
#   compute these aggregates via composite queries.
class Run(SQLModel, table=True):
    """Run model - represents an execution session.

    A run is executed by a specific agent instance (agent_checksum).
    Class-level runs are derived by aggregating all instance runs with the same cls_checksum.
    """

    __tablename__ = "run"

    id: UUID = Field(primary_key=True)
    agent_checksum: str = Field(
        foreign_key="agent_provenance.agent_checksum", index=True
    )
    # Agent class checksum is run-level invariant; kept here for convenience and
    # to avoid storing run-invariant data on every TaskResult row.
    agent_cls_checksum: str | None = Field(
        default=None, foreign_key="agent_class_provenance.cls_checksum", index=True
    )
    dataset_id: int | None = Field(default=None, foreign_key="dataset.id", index=True)
    timestamp_utc: datetime

    # Dashboard Stats (Calculated during ingestion)
    total_tasks: int = Field(default=0)
    success_count: int = Field(default=0)
    failure_count: int = Field(default=0)
    success_rate: float = Field(default=0.0)

    # Aggregated metrics
    total_tokens: int = Field(default=0)
    total_input_tokens: int = Field(default=0)
    total_output_tokens: int = Field(default=0)
    total_execution_time_sec: float = Field(default=0.0)
    total_llm_invocation_count: int = Field(default=0)

    is_best_run: bool = Field(
        default=False
    )  # Can be used to show which run to show on leaderboard for multiple runs.
    source_file_name: str | None = None

    # Relationships
    agent_instance: AgentProvenance = Relationship(back_populates="runs")
    agent_class: "AgentClassProvenance" = Relationship(back_populates="runs")
    results: list["TaskResultDB"] = Relationship(back_populates="run")
    tag_links: list[RunTagLink] = Relationship(back_populates="run")
    dataset: Dataset = Relationship(back_populates="runs")

# Notes re data model:
# - we don't need a dataset ID / project ID since task_ID has a uniquely associated
#   project ID
# - in the future we may want a richer status type, e.g. to capture execution
#   in the pipeline vs. agent failure during task attempt
class TaskResultDB(SQLModel, table=True):
    """
    TaskResultDB model - individual task result within a run.

    This mirrors the logical structure of `backend.models.TaskResult`,
    but is stored in the relational database.
    """

    __tablename__ = "taskresults"

    id: int | None = Field(default=None, primary_key=True)
    run_id: UUID = Field(foreign_key="run.id", index=True)
    task_id: int = Field(foreign_key="task.id", index=True)
    # Store the logical task name for queries that need to join on the original string
    task_name: str = Field(default="", index=True)
    trace_id: str | None = Field(default=None, index=True)

    timestamp_utc: datetime
    status: str  # 'Success' or 'Failure'

    # JSON fields - use sa_column for proper PostgreSQL JSON/JSONB support
    metrics: dict[str, Any] | None = Field(default=None, sa_column=Column(JSON))
    failure_reason: list[str] | None = Field(default=None, sa_column=Column(JSON))
    results: dict[str, Any] | None = Field(default=None, sa_column=Column(JSON))
    task_metadata: dict[str, Any] | None = Field(default=None, sa_column=Column(JSON))

    # Relationships
    run: Run = Relationship(back_populates="results")
    task: Task = Relationship(back_populates="results")
