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

from backend.db_models import Agent, Run, RunTagLink, Tag, Task, TaskResultDB
from backend.models import (
    AgentInfo,
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


def get_or_create_task(session: Session, task_id: str, kind: str | None = None) -> Task:
    """Fetch a Task by id or create it if missing."""
    task = session.get(Task, task_id)
    if task:
        if kind and task.kind != kind:
            task.kind = kind
        return task

    task = Task(id=task_id, kind=kind)
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


def _recompute_best_run_for_agent(session: Session, agent_id: int) -> None:
    """
    Recalculate which run is the "best" for a given agent based on
    a simple heuristic:

        score = success_rate * log(1 + total_tasks)
    """
    stmt = select(Run).where(Run.agent_id == agent_id)
    runs: list[Run] = list(session.exec(stmt).all())

    if not runs:
        return

    def score(run: Run) -> float:
        weight = math.log(1 + run.total_tasks) if run.total_tasks > 0 else 0.0
        return run.success_rate * weight

    best = max(runs, key=score)
    for run in runs:
        run.is_best_run = run.id == best.id


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
    - Ensures Agent and Task entities exist
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

    run = session.get(Run, run_uuid)

    if run is None:
        # Derive a reasonable timestamp for the run (earliest task timestamp)
        timestamps = [_parse_timestamp_utc(tr.timestamp_utc) for tr in task_results]
        earliest_ts = min(timestamps)

        run = Run(
            id=run_uuid,
            agent_id=agent.id,
            timestamp_utc=earliest_ts,
            source_file_name=source_file_name,
        )
        session.add(run)
        session.flush()
    else:
        # Update basic fields on re-ingestion
        run.agent_id = agent.id
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

        # Ensure task exists
        task = get_or_create_task(session, task_id=tr.task_id, kind=tr.task_kind)

        ts_utc = _parse_timestamp_utc(tr.timestamp_utc)

        metrics_dict = tr.metrics.model_dump(mode="json") if tr.metrics else None
        if tr.metrics:
            total_llm_invocation_count += tr.metrics.llm_invocation_count
            tc = tr.metrics.token_counts
            ru = tr.metrics.resource_usage

            total_tokens += tc.total_tokens
            total_input_tokens += tc.input_tokens
            total_output_tokens += tc.output_tokens
            total_execution_time_sec += ru.execution_time_sec

        # Normalise results payload to a JSON-serialisable dict where possible
        results_payload = tr.results
        if results_payload is not None and not isinstance(results_payload, dict):
            # Wrap non-dict result in a dict for more structured querying
            results_payload = {"value": results_payload}

        run_result = TaskResultDB(
            run_id=run.id,
            task_id=task.id,
            timestamp_utc=ts_utc,
            status=tr.status,
            metrics=metrics_dict,
            failure_reason=tr.failure_reason,
            results=results_payload,
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

    # Recompute "best run" flag for this agent
    # _recompute_best_run_for_agent(session, agent_id=agent.id)  # type: ignore[arg-type]

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

        # Compute score per run (success_rate * log(1 + total_tasks))
        def score(run: Run) -> float:
            weight = math.log(1 + run.total_tasks) if run.total_tasks > 0 else 0.0
            return run.success_rate * weight

        best_run_obj: Run | None = max(runs, key=score) if runs else None

        best_run_info: RunInfo | None = None
        if best_run_obj is not None:
            best_run_info = RunInfo(
                run_id=str(best_run_obj.id),
                agent_name=agent_name,
                timestamp_utc=best_run_obj.timestamp_utc.isoformat(),
                total_tasks=best_run_obj.total_tasks,
                success_count=best_run_obj.success_count,
                failure_count=best_run_obj.failure_count,
                success_rate=best_run_obj.success_rate,
                score=score(best_run_obj),
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
                metadata=TaskMetadata(),
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
        .order_by(Run.timestamp_utc.desc())  # type: ignore[arg-type]
    ).all()

    run_infos: list[RunInfo] = []

    for run in runs:
        run_infos.append(
            RunInfo(
                run_id=str(run.id),
                agent_name=agent_name,
                timestamp_utc=run.timestamp_utc.isoformat(),
                total_tasks=run.total_tasks,
                success_count=run.success_count,
                failure_count=run.failure_count,
                success_rate=run.success_rate,
                score=0.0,  # Score is not persisted; callers can compute if needed
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
                metadata=TaskMetadata(),
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

            if tr_db.metrics is None:
                # Skip tasks without metrics; they don't fit the TaskResult schema
                continue

            # Reconstruct Metrics from stored dict
            metrics = Metrics.model_validate(tr_db.metrics)

            tasks.append(
                TaskResult(
                    run_id=str(run.id),
                    task_kind=task_kind,
                    task_id=tr_db.task_id,
                    timestamp_utc=tr_db.timestamp_utc.isoformat(),
                    agent_name=agent_name,
                    status=tr_db.status,
                    metrics=metrics,
                    metadata=TaskMetadata(),
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


