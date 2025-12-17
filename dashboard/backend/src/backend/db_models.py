"""
SQLModel database models for the RAT Dashboard.
These models map directly to PostgreSQL tables.
"""
from datetime import UTC, datetime
from typing import Any
from uuid import UUID

from sqlalchemy import JSON, Column, Integer
from sqlmodel import Field, Relationship, SQLModel


class Agent(SQLModel, table=True):
    """Agent model - represents an AI agent being tested."""

    __tablename__ = "agent"

    id: int | None = Field(default=None, primary_key=True) # auto-generate
    name: str = Field(unique=True, index=True)
    description: str | None = None
    created_at: datetime | None = Field(default_factory=lambda: datetime.now(UTC))

    # Relationships
    runs: list["Run"] = Relationship(back_populates="agent")


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
    results: list["TaskResultDB"] = Relationship(back_populates="dataset")


class Task(SQLModel, table=True):
    """Task model - represents a problem/task being solved."""

    __tablename__ = "task"

    id: str = Field(primary_key=True)  # e.g., "ArrayCopy.v#lemma:test_ok"
    kind: str | None = None
    # Foreign key to Dataset; nullable for backward compatibility with
    # older ingested data that did not include dataset information.
    dataset_id: int | None = Field(foreign_key="dataset.id", index=True)
    difficulty_score: int = Field(default=0)

    # Relationships
    results: list["TaskResultDB"] = Relationship(back_populates="task")
    dataset: Dataset = Relationship(back_populates="tasks")


class Tag(SQLModel, table=True):
    """Tag model - metadata key-value pairs."""

    __tablename__ = "tag"

    id: int | None = Field(default=None, primary_key=True)
    key: str = Field(index=True)
    value: str

    # Relationships
    run_links: list["RunTagLink"] = Relationship(back_populates="tag")


class RunTagLink(SQLModel, table=True):
    """Link table for many-to-many relationship between runs and tags."""

    __tablename__ = "run_tag_link"

    run_id: UUID = Field(foreign_key="run.id", primary_key=True)
    tag_id: int = Field(foreign_key="tag.id", primary_key=True)

    # Relationships
    run: "Run" = Relationship(back_populates="tag_links")
    tag: Tag = Relationship(back_populates="run_links")


class Run(SQLModel, table=True):
    """Run model - represents an execution session."""

    __tablename__ = "run"

    id: UUID = Field(primary_key=True)
    agent_id: int = Field(foreign_key="agent.id", index=True)
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

    is_best_run: bool = Field(default=False) # Can be used to show which run to show on leaderboard for multiple runs.
    source_file_name: str | None = None

    # Relationships
    agent: Agent = Relationship(back_populates="runs")
    results: list["TaskResultDB"] = Relationship(back_populates="run")
    tag_links: list[RunTagLink] = Relationship(back_populates="run")
    dataset: Dataset = Relationship(back_populates="runs")


class TaskResultDB(SQLModel, table=True):
    """
    TaskResultDB model - individual task result within a run.

    This mirrors the logical structure of `backend.models.TaskResult`,
    but is stored in the relational database.
    """

    __tablename__ = "taskresults"

    id: int | None = Field(default=None, primary_key=True)
    run_id: UUID = Field(foreign_key="run.id", index=True)
    task_id: str = Field(foreign_key="task.id", index=True)
    dataset_id: int = Field(foreign_key="dataset.id", index=True)

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
    dataset: Dataset = Relationship(back_populates="results")
