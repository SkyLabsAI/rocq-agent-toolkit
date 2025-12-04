"""
Data Access Layer (DAL) for interacting with the PostgreSQL database.

This module encapsulates all database-facing logic so that FastAPI
endpoints can remain thin and focused on HTTP concerns.
"""

from __future__ import annotations

import math
from collections import defaultdict
from collections.abc import Iterable, Sequence
from datetime import UTC, datetime
from uuid import UUID

from sqlmodel import Session, delete, select

from backend.db_models import Agent, Dataset, Run, RunTagLink, Tag, Task, TaskResultDB
from backend.models import (
    AgentInfo,
    AgentWithRuns,
    DatasetAgentsResponse,
    DatasetInfo,
    Metrics,
    RunDetailsResponse,
    RunInfo,
    TagsResponse,
    TaskMetadata,
    TaskResult,
)


def _parse_timestamp_utc(ts: str) -> datetime:
    """
    Parse an ISO 8601 timestamp string into a datetime object.

    Accepts values with a trailing 'Z' or with an explicit offset.
    Falls back to naive parsing if timezone info is missing.
    """
    if not ts:
        # Fallback to "now" if timestamp is missing
        return datetime.now(UTC)

    normalised = ts.replace("Z", "+00:00") if ts.endswith("Z") else ts
    try:
        dt = datetime.fromisoformat(normalised)
    except ValueError:
        # Last resort: try parsing without timezone
        dt = datetime.fromisoformat(normalised.split(".")[0])

    # Ensure UTC-awareness
    if dt.tzinfo is None:
        return dt.replace(tzinfo=UTC)
    return dt.astimezone(UTC)

 # Compute score per run (success_rate * log(1 + total_tasks))
def compute_score(run: Run) -> float:
    weight = math.log(1 + run.total_tasks) if run.total_tasks > 0 else 0.0
    return run.success_rate * weight



def get_or_create_agent(session: Session, name: str, description: str | None = None) -> Agent:
    """Fetch an Agent by name or create it if missing."""
    stmt = select(Agent).where(Agent.name == name)
    agent = session.exec(stmt).first()
    if agent:
        if description and agent.description != description:
            agent.description = description
        return agent

    agent = Agent(name=name, description=description)
    session.add(agent)
    session.flush()
    return agent


def get_or_create_dataset(
    session: Session, name: str, description: str | None = None
) -> Dataset:
    """
    Fetch a Dataset by name or create it if missing.

    The logical identifier coming from JSONL (e.g. "loop_corpus") is stored
    in the `name` column; the primary key is an auto-generated integer.
    """
    stmt = select(Dataset).where(Dataset.name == name)
    dataset = session.exec(stmt).first()
    if dataset:
        if description and dataset.description != description:
            dataset.description = description
        return dataset

    dataset = Dataset(name=name, description=description)
    session.add(dataset)
    session.flush()
    return dataset


def get_or_create_task(
    session: Session, task_id: str, kind: str | None = None, dataset: Dataset | None = None
) -> Task:
    """Fetch a Task by id or create it if missing.

    If a Dataset is provided and the Task is newly created, it will be
    associated with that dataset. Existing tasks keep their dataset
    association to avoid surprising cross-dataset moves.
    """
    task = session.get(Task, task_id)
    if task:
        if kind and task.kind != kind:
            task.kind = kind
        # Only set dataset if it's currently unset; avoid overwriting an
        # existing association.
        if dataset is not None and task.dataset_id is None and dataset.id is not None:
            task.dataset_id = dataset.id
        return task

    task = Task(
        id=task_id,
        kind=kind,
        dataset_id=dataset.id if (dataset is not None and dataset.id is not None) else None,
    )
    session.add(task)
    session.flush()
    return task


def get_or_create_tag(session: Session, key: str, value: str) -> Tag:
    """Fetch a Tag by (key, value) or create it if missing."""
    stmt = select(Tag).where(Tag.key == key, Tag.value == value)
    tag = session.exec(stmt).first()
    if tag:
        return tag

    tag = Tag(key=key, value=value)
    session.add(tag)
    session.flush()
    return tag



def ingest_task_results_for_run(
    session: Session,
    run_id_str: str,
    agent_name: str,
    task_results: Sequence[TaskResult],
    source_file_name: str | None = None,
) -> Run:
    """
    Ingest a collection of TaskResult entries belonging to a single run.

    This function:
    - Ensures Agent, Dataset and Task entities exist
    - Creates or updates the Run row
    - Replaces all RunResult rows for that run
    - Aggregates metrics at the run level
    - Attaches tags to the run via Tag and RunTagLink
    - Recomputes the best run flag for the agent
    """
    if not task_results:
        raise ValueError("No task results provided for ingestion")

    run_uuid = UUID(run_id_str)

    # Ensure agent exists
    agent = get_or_create_agent(session, name=agent_name)
    if agent.id is None:
        raise ValueError("Agent must have a persisted primary key before creating runs")

    dataset_id = task_results[0].dataset_id or "default"
    dataset = get_or_create_dataset(session, name=dataset_id)

    run = session.get(Run, run_uuid)

    if run is None:
        # Derive a reasonable timestamp for the run (earliest task timestamp)
        timestamps = [_parse_timestamp_utc(tr.timestamp_utc) for tr in task_results]
        earliest_ts = min(timestamps)

        run = Run(
            id=run_uuid,
            agent_id=agent.id,
            dataset_id=dataset.id,
            timestamp_utc=earliest_ts,
            source_file_name=source_file_name,
        )
        session.add(run)
        session.flush()
    else:
        # Update basic fields on re-ingestion
        run.agent_id = agent.id
        run.dataset_id = dataset.id
        if source_file_name:
            run.source_file_name = source_file_name

        # Remove existing results for this run so we can replace them
        session.exec(delete(TaskResultDB).where(TaskResultDB.run_id == run.id))

    # Aggregation accumulators
    total_tasks = 0
    success_count = 0
    failure_count = 0
    total_tokens = 0
    total_input_tokens = 0
    total_output_tokens = 0
    total_execution_time_sec = 0.0
    total_llm_invocation_count = 0

    # Collect tags across all tasks
    tag_pairs: set[tuple[str, str]] = set()

    # Insert TaskResultDB rows
    for tr in task_results:
        total_tasks += 1
        if tr.status == "Success":
            success_count += 1
        elif tr.status == "Failure":
            failure_count += 1

        # Ensure dataset and task exist
        task = get_or_create_task(session, task_id=tr.task_id, kind=tr.task_kind, dataset=dataset)

        ts_utc = _parse_timestamp_utc(tr.timestamp_utc)

        metrics_dict = tr.metrics.model_dump(mode="json") if tr.metrics else None
        metadata_dict = tr.metadata.model_dump(mode="json") if tr.metadata else None
        if tr.metrics:
            total_llm_invocation_count += tr.metrics.llm_invocation_count
            tc = tr.metrics.token_counts
            ru = tr.metrics.resource_usage

            total_tokens += tc.total_tokens
            total_input_tokens += tc.input_tokens
            total_output_tokens += tc.output_tokens
            total_execution_time_sec += ru.execution_time_sec

        run_result = TaskResultDB(
            run_id=run.id,
            task_id=task.id,
            dataset_id=dataset.id,
            timestamp_utc=ts_utc,
            status=tr.status,
            metrics=metrics_dict,
            failure_reason=tr.failure_reason,
            results=tr.results,
            task_metadata=metadata_dict,
        )
        session.add(run_result)

        # Accumulate tags
        if tr.metadata and tr.metadata.tags:
            for key, value in tr.metadata.tags.items():
                tag_pairs.add((key, str(value)))

    # Compute run-level aggregates
    run.total_tasks = total_tasks
    run.success_count = success_count
    run.failure_count = failure_count
    run.success_rate = (success_count / total_tasks) if total_tasks > 0 else 0.0
    run.total_tokens = total_tokens
    run.total_input_tokens = total_input_tokens
    run.total_output_tokens = total_output_tokens
    run.total_execution_time_sec = total_execution_time_sec
    run.total_llm_invocation_count = total_llm_invocation_count

    # Attach tags at the run level
    # First, clear existing links to avoid duplicates on re-ingestion
    session.exec(delete(RunTagLink).where(RunTagLink.run_id == run.id))

    for key, value in sorted(tag_pairs):
        tag = get_or_create_tag(session, key=key, value=value)

        link_stmt = select(RunTagLink).where(
            RunTagLink.run_id == run.id,
            RunTagLink.tag_id == tag.id,
        )
        existing_link = session.exec(link_stmt).first()
        if existing_link is None:
            session.add(RunTagLink(run_id=run.id, tag_id=tag.id))


    return run


def ingest_task_results(
    session: Session,
    task_results: Iterable[TaskResult],
    source_file_name: str | None = None,
) -> dict[str, int]:
    """
    Ingest an arbitrary collection of TaskResult entries which may span
    multiple runs and/or agents.

    Returns basic statistics about the ingestion.
    """
    # Group by (run_id, agent_name)
    grouped: dict[tuple[str, str], list[TaskResult]] = defaultdict(list)
    total_tasks = 0

    for tr in task_results:
        key = (tr.run_id, tr.agent_name)
        grouped[key].append(tr)
        total_tasks += 1

    runs_ingested = 0
    for (run_id, agent_name), group in grouped.items():
        ingest_task_results_for_run(
            session=session,
            run_id_str=run_id,
            agent_name=agent_name,
            task_results=group,
            source_file_name=source_file_name,
        )
        runs_ingested += 1

    return {"runs_ingested": runs_ingested, "tasks_ingested": total_tasks}


def _get_tags_for_run(session: Session, run_id: UUID) -> dict[str, str]:
    """
    Helper to reconstruct metadata tags for a run from Tag/RunTagLink tables.

    If multiple values exist for the same key, the last one seen wins.
    """
    rows = session.exec(
        select(Tag.key, Tag.value)
        .join(RunTagLink, RunTagLink.tag_id == Tag.id)
        .where(RunTagLink.run_id == run_id)
    ).all()

    tags: dict[str, str] = {}
    for key, value in rows:
        tags[key] = value
    return tags


def _get_dataset_name_for_run(session: Session, run: Run) -> str | None:
    """
    Helper to resolve the logical dataset identifier (Dataset.name) for a run.

    Returns None if no dataset is associated with the run or the Dataset row
    cannot be found (for backward compatibility with older ingestions).
    """
    if run.dataset_id is None:
        return None

    ds = session.get(Dataset, run.dataset_id)
    if ds is None:
        return None
    return ds.name

def agent_exists(session: Session, agent_name: str) -> bool:
    """Return True if an agent with the given name exists."""
    return session.exec(
        select(Agent.id).where(Agent.name == agent_name)
    ).first() is not None


def list_agents_from_db(session: Session) -> list[AgentInfo]:
    """
    List all agents with their total run counts and best run information.

    This mirrors the behaviour of DataStore.get_all_agents, but is backed
    by the relational database.
    """
    # Load all runs joined with their agents
    rows = session.exec(
        select(Run, Agent).join(Agent, Run.agent_id == Agent.id)  # type: ignore[arg-type]
    ).all()

    # Group runs by agent name
    grouped: dict[str, list[Run]] = {}
    agent_by_name: dict[str, Agent] = {}

    for run, agent in rows:
        agent_by_name[agent.name] = agent
        grouped.setdefault(agent.name, []).append(run)

    agent_infos: list[AgentInfo] = []

    for agent_name, runs in sorted(grouped.items(), key=lambda x: x[0]):
        total_runs = len(runs)

        # Prefer the run explicitly marked as best in the database, if any.
        # Fallback to the highest-scoring run if no flag is set.
        best_run_obj: Run | None = next((r for r in runs if r.is_best_run), None)
        if best_run_obj is None and runs:
            best_run_obj = max(runs, key=compute_score)

        best_run_info: RunInfo | None = None
        if best_run_obj is not None:
            best_run_tags = _get_tags_for_run(session, best_run_obj.id)
            best_run_dataset_name = _get_dataset_name_for_run(session, best_run_obj)
            best_run_info = RunInfo(
                run_id=str(best_run_obj.id),
                agent_name=agent_name,
                timestamp_utc=best_run_obj.timestamp_utc.isoformat(),
                dataset_id=best_run_dataset_name,
                total_tasks=best_run_obj.total_tasks,
                success_count=best_run_obj.success_count,
                failure_count=best_run_obj.failure_count,
                success_rate=best_run_obj.success_rate,
                score=compute_score(best_run_obj),
                avg_total_tokens=(
                    best_run_obj.total_tokens / best_run_obj.total_tasks
                    if best_run_obj.total_tasks
                    else 0.0
                ),
                avg_llm_invocation_count=(
                    best_run_obj.total_llm_invocation_count / best_run_obj.total_tasks
                    if best_run_obj.total_tasks
                    else 0.0
                ),
                avg_cpu_time_sec=(
                    best_run_obj.total_execution_time_sec / best_run_obj.total_tasks
                    if best_run_obj.total_tasks
                    else 0.0
                ),
                best_run=best_run_obj.is_best_run,
                metadata=TaskMetadata(tags=best_run_tags),
            )

        agent_infos.append(
            AgentInfo(agent_name=agent_name, total_runs=total_runs, best_run=best_run_info)
        )

    return agent_infos


def get_runs_by_agent_from_db(session: Session, agent_name: str) -> list[RunInfo]:
    """
    Get all runs for a specific agent, sorted by timestamp (most recent first).
    """
    agent = session.exec(select(Agent).where(Agent.name == agent_name)).first()
    if agent is None:
        return []

    runs = session.exec(
        select(Run)
        .where(Run.agent_id == agent.id)
        .order_by(Run.timestamp_utc.desc())
    ).all()

    run_infos: list[RunInfo] = []

    for run in runs:
        run_tags = _get_tags_for_run(session, run.id)
        dataset_name = _get_dataset_name_for_run(session, run)
        run_infos.append(
            RunInfo(
                run_id=str(run.id),
                agent_name=agent_name,
                timestamp_utc=run.timestamp_utc.isoformat(),
                dataset_id=dataset_name,
                total_tasks=run.total_tasks,
                success_count=run.success_count,
                failure_count=run.failure_count,
                success_rate=run.success_rate,
                score=compute_score(run),
                avg_total_tokens=(
                    run.total_tokens / run.total_tasks if run.total_tasks else 0.0
                ),
                avg_llm_invocation_count=(
                    run.total_llm_invocation_count / run.total_tasks
                    if run.total_tasks
                    else 0.0
                ),
                avg_cpu_time_sec=(
                    run.total_execution_time_sec / run.total_tasks
                    if run.total_tasks
                    else 0.0
                ),
                best_run=run.is_best_run,
                metadata=TaskMetadata(tags=run_tags),
            )
        )

    return run_infos


def get_runs_by_agent_and_dataset_from_db(
    session: Session, agent_name: str, dataset_id: str
) -> list[RunInfo] | None:
    """
    Get all runs for a specific agent within a specific dataset, sorted by
    timestamp (most recent first).
    """
    agent = session.exec(select(Agent).where(Agent.name == agent_name)).first()
    if agent is None:
        # Agent does not exist; let the caller decide how to handle this.
        return []

    dataset = session.exec(select(Dataset).where(Dataset.name == dataset_id)).first()
    if dataset is None:
        # Dataset does not exist; signal this with None so the caller can
        # distinguish it from "no runs yet".
        return None

    runs = session.exec(
        select(Run)
        .where(Run.agent_id == agent.id, Run.dataset_id == dataset.id)
        .order_by(Run.timestamp_utc.desc())  # type: ignore[arg-type]
    ).all()

    run_infos: list[RunInfo] = []

    for run in runs:
        run_tags = _get_tags_for_run(session, run.id)
        dataset_name = _get_dataset_name_for_run(session, run)
        run_infos.append(
            RunInfo(
                run_id=str(run.id),
                agent_name=agent_name,
                timestamp_utc=run.timestamp_utc.isoformat(),
                dataset_id=dataset_name,
                total_tasks=run.total_tasks,
                success_count=run.success_count,
                failure_count=run.failure_count,
                success_rate=run.success_rate,
                score=compute_score(run),
                avg_total_tokens=(
                    run.total_tokens / run.total_tasks if run.total_tasks else 0.0
                ),
                avg_llm_invocation_count=(
                    run.total_llm_invocation_count / run.total_tasks
                    if run.total_tasks
                    else 0.0
                ),
                avg_cpu_time_sec=(
                    run.total_execution_time_sec / run.total_tasks
                    if run.total_tasks
                    else 0.0
                ),
                best_run=run.is_best_run,
                metadata=TaskMetadata(tags=run_tags),
            )
        )

    return run_infos


def get_run_details_from_db(session: Session, run_ids: list[str]) -> list[RunDetailsResponse]:
    """
    Get complete details for one or more runs.
    """
    responses: list[RunDetailsResponse] = []

    for run_id_str in run_ids:
        try:
            run_uuid = UUID(run_id_str)
        except ValueError:
            continue

        run = session.get(Run, run_uuid)
        if run is None:
            continue

        agent = session.get(Agent, run.agent_id)
        agent_name = agent.name if agent else "Unknown"

        task_results_db = session.exec(
            select(TaskResultDB)
            .where(TaskResultDB.run_id == run.id)
            .order_by(TaskResultDB.timestamp_utc)  # type: ignore[arg-type]
        ).all()

        tasks: list[TaskResult] = []
        for tr_db in task_results_db:
            task = session.get(Task, tr_db.task_id)
            task_kind = (task.kind or "") if task else ""

            # Reconstruct dataset identifier as exposed via the JSONL API.
            # Prefer the Task's dataset (and its Dataset.name); if missing,
            # fall back to the Run-level dataset, if any.
            dataset_name: str | None = None
            if task is not None and task.dataset_id is not None:
                ds = session.get(Dataset, task.dataset_id)
                if ds is not None:
                    dataset_name = ds.name
            if dataset_name is None and run.dataset_id is not None:
                ds = session.get(Dataset, run.dataset_id)
                if ds is not None:
                    dataset_name = ds.name

            if tr_db.metrics is None:
                # Skip tasks without metrics; they don't fit the TaskResult schema
                continue

            # Reconstruct Metrics from stored dict
            metrics = Metrics.model_validate(tr_db.metrics)

            # Reconstruct TaskMetadata (including tags and any extra fields)
            metadata = (
                TaskMetadata.model_validate(tr_db.task_metadata)
                if tr_db.task_metadata is not None
                else TaskMetadata()
            )

            tasks.append(
                TaskResult(
                    run_id=str(run.id),
                    task_kind=task_kind,
                    task_id=tr_db.task_id,
                    dataset_id=dataset_name,
                    timestamp_utc=tr_db.timestamp_utc.isoformat(),
                    agent_name=agent_name,
                    status=tr_db.status,
                    metrics=metrics,
                    metadata=metadata,
                    results=tr_db.results,
                    failure_reason=tr_db.failure_reason,
                )
            )

        responses.append(
            RunDetailsResponse(
                run_id=str(run.id),
                agent_name=agent_name,
                total_tasks=len(tasks),
                tasks=tasks,
            )
        )

    return responses


def get_unique_tags_from_db(session: Session) -> TagsResponse:
    """
    Get all unique metadata tag keys and their unique values across runs.
    """
    tags: dict[str, set[str]] = {}

    for tag in session.exec(select(Tag)).all():
        tags.setdefault(tag.key, set()).add(tag.value)

    tags_sorted: dict[str, list[str]] = {
        key: sorted(values) for key, values in tags.items()
    }

    total_keys = len(tags_sorted)
    total_values = sum(len(values) for values in tags_sorted.values())

    return TagsResponse(tags=tags_sorted, total_keys=total_keys, total_values=total_values)


def list_datasets_from_db(session: Session) -> list[DatasetInfo]:
    """
    List all datasets stored in the database.

    Returns them as DatasetInfo objects exposing the logical identifier
    (Dataset.name) as dataset_id.
    """
    datasets: list[Dataset] = session.exec(
        select(Dataset).order_by(Dataset.name)  # type: ignore[arg-type]
    ).all()

    result: list[DatasetInfo] = []
    for ds in datasets:
        created_at_str = ds.created_at.isoformat() if ds.created_at is not None else None
        result.append(
            DatasetInfo(
                dataset_id=ds.name,
                description=ds.description,
                created_at=created_at_str,
            )
        )
    return result


def get_agents_for_dataset_from_db(
    session: Session, dataset_id: str
) -> DatasetAgentsResponse | None:
    """
    Get all agents that have at least one run for the given dataset.

    The dataset is identified by its logical identifier (Dataset.name), which
    corresponds to the JSONL `dataset_id` field (e.g. "loop_corpus").
    """
    dataset = session.exec(
        select(Dataset).where(Dataset.name == dataset_id)
    ).first()
    if dataset is None:
        return None

    # Load all runs for this dataset joined with their agents
    rows = session.exec(
        select(Run, Agent)
        .join(Agent, Run.agent_id == Agent.id)  # type: ignore[arg-type]
        .where(Run.dataset_id == dataset.id)
    ).all()

    if not rows:
        # Dataset exists but currently has no runs; return empty structure.
        return DatasetAgentsResponse(dataset_id=dataset.name, agents=[])

    # Group runs by agent name
    agents_runs: dict[str, list[Run]] = {}
    for run, agent in rows:
        agents_runs.setdefault(agent.name, []).append(run)

    agents: list[AgentWithRuns] = []

    for agent_name, runs in sorted(agents_runs.items(), key=lambda x: x[0]):
        # Collect all run_ids for this agent within the dataset
        run_ids = sorted(str(run.id) for run in runs)

        # Prefer the run explicitly marked as best in the database, if any.
        # This flag is global per agent; if the best run lives in another
        # dataset, there may be no flagged run in this subset, in which case
        # we fall back to the highest-scoring run for this dataset only.
        best_run_obj: Run | None = next((r for r in runs if r.is_best_run), None)
        if best_run_obj is None and runs:
            best_run_obj = max(runs, key=compute_score)

        best_run_info: RunInfo | None = None
        if best_run_obj is not None:
            best_run_tags = _get_tags_for_run(session, best_run_obj.id)
            best_run_dataset_name = _get_dataset_name_for_run(session, best_run_obj)
            best_run_info = RunInfo(
                run_id=str(best_run_obj.id),
                agent_name=agent_name,
                timestamp_utc=best_run_obj.timestamp_utc.isoformat(),
                dataset_id=best_run_dataset_name,
                total_tasks=best_run_obj.total_tasks,
                success_count=best_run_obj.success_count,
                failure_count=best_run_obj.failure_count,
                success_rate=best_run_obj.success_rate,
                score=compute_score(best_run_obj),
                avg_total_tokens=(
                    best_run_obj.total_tokens / best_run_obj.total_tasks
                    if best_run_obj.total_tasks
                    else 0.0
                ),
                avg_llm_invocation_count=(
                    best_run_obj.total_llm_invocation_count / best_run_obj.total_tasks
                    if best_run_obj.total_tasks
                    else 0.0
                ),
                avg_cpu_time_sec=(
                    best_run_obj.total_execution_time_sec / best_run_obj.total_tasks
                    if best_run_obj.total_tasks
                    else 0.0
                ),
                best_run=best_run_obj.is_best_run,
                metadata=TaskMetadata(tags=best_run_tags),
            )

        agents.append(
            AgentWithRuns(
                agent_name=agent_name,
                run_ids=run_ids,
                best_run=best_run_info,
            )
        )

    return DatasetAgentsResponse(dataset_id=dataset.name, agents=agents)


def set_best_run_flag_for_run(session: Session, run_id: str, best_run: bool) -> bool:
    """
    Set or unset the 'best run' flag for a specific run.

    Args:
        session: Database session.
        run_id: String representation of the run UUID.
        best_run: Boolean flag indicating whether this run is the best run.

    Returns:
        The updated boolean value of the best-run flag.

    Raises:
        ValueError: If the run_id is not a valid UUID format.
        LookupError: If no run with the given ID exists.
    """
    try:
        run_uuid = UUID(run_id)
    except ValueError as e:
        raise ValueError(f"Invalid run_id format: {run_id}") from e

    run = session.get(Run, run_uuid)
    if run is None:
        raise LookupError(f"Run with id '{run_id}' not found")

    # Update the best-run flag
    run.is_best_run = best_run
    return run.is_best_run


def get_estimated_time_for_task_from_db(
    session: Session, run_id: str, task_id: str
) -> datetime | None:
    """
    Estimate when logs were generated for a given run and task based on
    the `timestamp_utc` field from the corresponding TaskResultDB row.

    We look for the matching (run_id, task_id) pair in the database and
    return its timestamp. If no exact match is found, we fall back to
    the run's own timestamp.
    """
    try:
        run_uuid = UUID(run_id)
    except ValueError:
        return None

    # Prefer the task-level timestamp when available
    tr_db = session.exec(
        select(TaskResultDB)
        .where(TaskResultDB.run_id == run_uuid, TaskResultDB.task_id == task_id)
        .order_by(TaskResultDB.timestamp_utc)  # type: ignore[arg-type]
    ).first()

    timestamp: datetime | None = None

    if tr_db is not None:
        timestamp = tr_db.timestamp_utc
    else:
        # Fallback to the run-level timestamp
        run = session.get(Run, run_uuid)
        if run is not None:
            timestamp = run.timestamp_utc

    if timestamp is None:
        return None

    # Ensure UTC-awareness
    if timestamp.tzinfo is None:
        return timestamp.replace(tzinfo=UTC)
    return timestamp.astimezone(UTC)


