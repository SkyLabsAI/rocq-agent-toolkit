"""
Data Access Layer (DAL) for interacting with the PostgreSQL database.

This module encapsulates all database-facing logic so that FastAPI
endpoints can remain thin and focused on HTTP concerns.
"""

from __future__ import annotations

import logging
import math
from collections import defaultdict
from collections.abc import Iterable, Sequence
from datetime import UTC, datetime
from typing import Any, cast
from uuid import UUID

import yaml
from sqlalchemy import desc
from sqlalchemy.sql.elements import ColumnElement
from sqlmodel import Session, delete, select

from backend.db_models import (
    AgentClassProvenance,
    AgentProvenance,
    Dataset,
    Run,
    RunTagLink,
    Tag,
    Task,
    TaskResultDB,
    TaskTagLink,
)
from backend.models import (
    AgentClassSummary,
    AgentInstanceSummary,
    AgentTaskRunsResponse,
    BulkAddTagsResponse,
    DatasetInfo,
    DatasetResultsAgentInstance,
    DatasetResultsResponse,
    DatasetResultsTask,
    DatasetTaskResult,
    DatasetTasksResponse,
    Metrics,
    RunDetailsResponse,
    RunInfo,
    TagsResponse,
    TaskDetailsResponse,
    TaskInfo,
    TaskMetadata,
    TaskResult,
)
from backend.provenance import (
    extract_provenance_from_logs_async,
    ingest_agent_class_provenance,
    ingest_agent_provenance,
)

logger = logging.getLogger(__name__)


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


def get_or_create_dataset(
    session: Session,
    name: str,
    description: str | None = None,
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
    session: Session,
    task_name: str,
    dataset: Dataset,
    kind: str | None = None,
    ground_truth: str | None = None,
) -> Task:
    """Fetch a Task by (name, dataset_id) or create it if missing.

    Tasks are unique per dataset.
    """
    # Look up by (name, dataset_id) combination
    stmt = select(Task).where(Task.name == task_name, Task.dataset_id == dataset.id)
    task = session.exec(stmt).first()

    if task:
        task_updated = False
        if kind is not None and task.kind != kind:
            task.kind = kind
            task_updated = True
        if ground_truth is not None and task.ground_truth != ground_truth:
            task.ground_truth = ground_truth
            task_updated = True
        if task_updated:
            session.flush()
        return task

    task = Task(
        name=task_name,
        kind=kind,
        dataset_id=dataset.id,
    )
    if ground_truth is not None:
        task.ground_truth = ground_truth
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


# Prefix used to identify task-level tags in the metadata
TASK_TAG_PREFIX = "TASK_"


def link_tag_to_task(session: Session, task: Task, tag: Tag) -> None:
    """Create a TaskTagLink if it doesn't already exist."""
    if task.id is None:
        return

    link_stmt = select(TaskTagLink).where(
        TaskTagLink.task_id == task.id,
        TaskTagLink.tag_id == tag.id,
    )
    existing_link = session.exec(link_stmt).first()
    if existing_link is None:
        session.add(TaskTagLink(task_id=task.id, tag_id=tag.id))


def get_tags_for_task(session: Session, task_id: int) -> dict[str, str]:
    """
    Helper to reconstruct metadata tags for a task from Tag/TaskTagLink tables.

    If multiple values exist for the same key, the last one seen wins.
    """
    rows = session.exec(
        select(Tag.key, Tag.value)
        .join(TaskTagLink, TaskTagLink.tag_id == Tag.id)  # type: ignore[arg-type]
        .where(TaskTagLink.task_id == task_id)
    ).all()

    tags: dict[str, str] = {}
    for key, value in rows:
        tags[key] = value
    return tags


def export_dataset_tasks_yaml_from_db(
    session: Session,
    dataset_id: str,
    tag: str | None = None,
) -> str | None:
    """
    Export a dataset's tasks as YAML, optionally filtered by a tag.

    Only tags with key == value are emitted to match the YAML ingestion format.
    """
    dataset = session.exec(select(Dataset).where(Dataset.name == dataset_id)).first()
    if dataset is None:
        return None

    task_stmt = select(Task).where(Task.dataset_id == dataset.id)
    tag_filter = tag.strip() if tag else None
    if tag_filter:
        task_stmt = (
            task_stmt.join(TaskTagLink, TaskTagLink.task_id == Task.id)  # type: ignore[arg-type]
            .join(Tag, Tag.id == TaskTagLink.tag_id)  # type: ignore[arg-type]
            .where(Tag.key == tag_filter, Tag.value == tag_filter)
        )

    tasks_db = session.exec(task_stmt.order_by(Task.name)).all()

    tasks_payload: list[dict[str, Any]] = []
    for task in tasks_db:
        if "#" in task.name:
            file_path, locator = task.name.split("#", 1)
        else:
            file_path = task.name
            locator = ""

        task_tags = get_tags_for_task(session, task.id) if task.id else {}
        yaml_tags = sorted(key for key, value in task_tags.items() if key == value)

        task_entry: dict[str, Any] = {
            "file": file_path,
            "locator": locator,
        }
        if yaml_tags:
            task_entry["tags"] = yaml_tags
        if task.kind:
            task_entry["kind"] = task.kind
        if task.ground_truth is not None:
            task_entry["ground_truth"] = task.ground_truth

        tasks_payload.append(task_entry)

    project_payload: dict[str, Any] = {"name": dataset.name}

    payload = {
        "project": project_payload,
        "tasks": tasks_payload,
    }

    return yaml.safe_dump(payload, sort_keys=False)


def _sync_task_tags(
    session: Session, task: Task, desired_tags: set[str]
) -> tuple[int, int]:
    """
    Sync task tags (key=value) to the desired set.

    Only tags where key == value are managed here, so tags from other sources
    (e.g., TaskResult metadata with distinct key/value) are preserved.
    """
    if task.id is None:
        return (0, 0)

    existing_rows = session.exec(
        select(Tag.id, Tag.key, Tag.value)
        .join(TaskTagLink, TaskTagLink.tag_id == Tag.id)  # type: ignore[arg-type]
        .where(TaskTagLink.task_id == task.id)
    ).all()

    managed_existing_ids: dict[str, int] = {
        key: tag_id
        for tag_id, key, value in existing_rows
        if tag_id is not None and key == value
    }

    tags_added = 0
    for tag_str in sorted(desired_tags):
        if not tag_str:
            continue
        tag = get_or_create_tag(session, key=tag_str, value=tag_str)
        link_stmt = select(TaskTagLink).where(
            TaskTagLink.task_id == task.id,
            TaskTagLink.tag_id == tag.id,
        )
        existing_link = session.exec(link_stmt).first()
        if existing_link is None:
            session.add(TaskTagLink(task_id=task.id, tag_id=tag.id))
            tags_added += 1

    to_remove_ids = [
        tag_id
        for key, tag_id in managed_existing_ids.items()
        if key not in desired_tags
    ]
    tags_removed = 0
    if to_remove_ids:
        session.exec(
            delete(TaskTagLink).where(
                cast(ColumnElement[bool], TaskTagLink.task_id == task.id),
                TaskTagLink.tag_id.in_(to_remove_ids),  # type: ignore[attr-defined]
            )
        )
        tags_removed = len(to_remove_ids)

    return (tags_added, tags_removed)


def ingest_task_dataset_from_yaml(
    session: Session,
    yaml_content: str,
) -> dict[str, Any]:
    """
    Ingest dataset/task definitions from a YAML payload.

    The YAML is expected to contain:
      - project.name: dataset identifier
      - tasks: list of task entries with file, locator, optional ground_truth, tags
    """
    try:
        payload = yaml.safe_load(yaml_content)
    except yaml.YAMLError as e:
        raise ValueError(f"Invalid YAML payload: {e}") from e

    if not isinstance(payload, dict):
        raise ValueError("YAML root must be a mapping")

    project = payload.get("project")
    if not isinstance(project, dict):
        raise ValueError("Missing 'project' mapping in YAML payload")

    dataset_name = project.get("name")
    if not dataset_name:
        raise ValueError("Missing 'project.name' in YAML payload")

    tasks = payload.get("tasks", [])
    if not isinstance(tasks, list):
        raise ValueError("YAML 'tasks' must be a list")

    dataset = get_or_create_dataset(session, name=str(dataset_name))

    tasks_created = 0
    tasks_updated = 0
    tags_added = 0
    tags_removed = 0

    for idx, task_entry in enumerate(tasks):
        if not isinstance(task_entry, dict):
            raise ValueError(f"Task entry at index {idx} must be a mapping")

        file_path = task_entry.get("file")
        locator = task_entry.get("locator")
        if not file_path or not locator:
            raise ValueError("Each task entry must include 'file' and 'locator' fields")

        task_name = f"{file_path}#{locator}"
        task_kind = task_entry.get("kind")

        existing_task = session.exec(
            select(Task).where(Task.name == task_name, Task.dataset_id == dataset.id)
        ).first()

        created = False
        task_changed = False
        if existing_task is None:
            existing_task = Task(
                name=task_name,
                kind=task_kind,
                dataset_id=dataset.id,
            )
            if "ground_truth" in task_entry:
                raw_ground_truth = task_entry.get("ground_truth")
                existing_task.ground_truth = (
                    None if raw_ground_truth is None else str(raw_ground_truth)
                )
            session.add(existing_task)
            session.flush()
            created = True
            tasks_created += 1
        else:
            if task_kind is not None and existing_task.kind != task_kind:
                existing_task.kind = task_kind
                task_changed = True
            if "ground_truth" in task_entry:
                raw_ground_truth = task_entry.get("ground_truth")
                ground_truth_value = (
                    None if raw_ground_truth is None else str(raw_ground_truth)
                )
                if existing_task.ground_truth != ground_truth_value:
                    existing_task.ground_truth = ground_truth_value
                    task_changed = True

        if "tags" in task_entry:
            raw_tags = task_entry.get("tags")
            if raw_tags is None:
                desired_tags: set[str] = set()
            elif isinstance(raw_tags, list):
                desired_tags = {
                    str(tag).strip() for tag in raw_tags if str(tag).strip()
                }
            else:
                raise ValueError(f"Task entry at index {idx} has invalid 'tags' type")

            added_count, removed_count = _sync_task_tags(
                session, existing_task, desired_tags
            )
            tags_added += added_count
            tags_removed += removed_count
            if (added_count or removed_count) and not created:
                task_changed = True

        if task_changed:
            tasks_updated += 1

    session.flush()

    return {
        "dataset_id": str(dataset.name),
        "tasks_created": tasks_created,
        "tasks_updated": tasks_updated,
        "tags_added": tags_added,
        "tags_removed": tags_removed,
    }


async def ingest_task_results_for_run(
    session: Session,
    run_id_str: str,
    task_results: Sequence[TaskResult],
    source_file_name: str | None = None,
) -> Run:
    """
    Ingest a collection of TaskResult entries belonging to a single run.

    This function:
    - Extracts provenance from observability logs and stores in DB
    - Ensures Dataset and Task entities exist
    - Creates or updates the Run row
    - Replaces all RunResult rows for that run
    - Aggregates metrics at the run level
    - Attaches tags to the run via Tag and RunTagLink
    - Recomputes the best run flag for the agent class
    """
    if not task_results:
        raise ValueError("No task results provided for ingestion")

    run_uuid = UUID(run_id_str)

    # Extract checksums from first task result (all should have same checksums for a run)
    first_tr = task_results[0]
    agent_checksum = first_tr.agent_checksum  # Run belongs to the instance
    agent_cls_checksum = first_tr.agent_cls_checksum
    timestamp_utc = _parse_timestamp_utc(first_tr.timestamp_utc)
    # During ingestion, task_id is always a string (from JSONL)
    first_task_id = str(
        first_tr.task_id
    )  # this is used to extract provenance from logs

    # Extract and ingest provenance from observability logs.
    #
    # For a given run, the agent instance/class checksums are identical across all
    # TaskResults, so we do not need to query logs for every task in the run.
    # We use the first task's timestamp as `estimated_time` to narrow the Loki
    # query window without consulting the DB (which is not yet populated during
    # ingestion).
    try:
        class_prov, instance_prov = await extract_provenance_from_logs_async(
            run_id_str, first_task_id, estimated_time=timestamp_utc
        )

        # Ingest class provenance
        for cls_checksum, prov_data in class_prov.items():
            try:
                ingest_agent_class_provenance(
                    session,
                    cls_checksum=cls_checksum,
                    cls_name=prov_data["cls_name"],
                    cls_provenance=prov_data["cls_provenance"],
                )
            except ValueError as e:
                # Collision detected - log and continue
                # The existing record will be used
                import logging

                logging.getLogger(__name__).warning("Provenance collision: %s", e)

        # Ingest instance provenance
        for agent_checksum_val, prov_data in instance_prov.items():
            try:
                # Extract cls_checksum from provenance data (logged in task_runner)
                cls_checksum = prov_data.get("cls_checksum", "")
                if not cls_checksum:
                    # This handles cases where class provenance was logged but instance wasn't
                    import logging

                    logging.getLogger(__name__).warning(
                        "Missing cls_checksum in AgentProvenance for %s",
                        agent_checksum_val,
                    )

                ingest_agent_provenance(
                    session,
                    agent_checksum=agent_checksum_val,
                    cls_checksum=cls_checksum,
                    name=prov_data["name"],
                    provenance=prov_data["provenance"],
                )
            except ValueError as e:
                # Collision detected - log and continue
                import logging

                logging.getLogger(__name__).warning("Provenance collision: %s", e)
    except Exception as e:  # pylint: disable=broad-exception-caught
        # Log error but continue with ingestion
        import logging

        logging.getLogger(__name__).warning(
            "Error extracting provenance for run_id=%s, task_id=%s: %s",
            run_id_str,
            first_task_id,
            e,
        )

    # Fallback: Create minimal provenance records from TaskResult data if extraction failed
    # This ensures AgentProvenance records exist even when observability logs aren't available
    first_tr = task_results[0]
    agent_checksum = first_tr.agent_checksum
    agent_cls_checksum = first_tr.agent_cls_checksum

    # Check if AgentProvenance exists, create if not
    existing_instance = session.exec(
        select(AgentProvenance).where(AgentProvenance.agent_checksum == agent_checksum)
    ).first()
    if existing_instance is None:
        # Create minimal AgentClassProvenance if it doesn't exist
        existing_class = session.exec(
            select(AgentClassProvenance).where(
                AgentClassProvenance.cls_checksum == agent_cls_checksum
            )
        ).first()
        if existing_class is None:
            ingest_agent_class_provenance(
                session,
                cls_checksum=agent_cls_checksum,
                cls_name=agent_cls_checksum,  # Use checksum as name fallback
                cls_provenance={},
            )

        # Create minimal AgentProvenance
        ingest_agent_provenance(
            session,
            agent_checksum=agent_checksum,
            cls_checksum=agent_cls_checksum,
            name=agent_checksum,  # Use checksum as name fallback
            provenance={},
        )

    dataset_id = task_results[0].dataset_id or "default"
    dataset = get_or_create_dataset(session, name=dataset_id)

    run = session.get(Run, run_uuid)

    if run is None:
        # Derive a reasonable timestamp for the run (earliest task timestamp)
        timestamps = [_parse_timestamp_utc(tr.timestamp_utc) for tr in task_results]
        earliest_ts = min(timestamps)

        run = Run(
            id=run_uuid,
            agent_checksum=agent_checksum,  # Run belongs to the instance
            agent_cls_checksum=agent_cls_checksum,
            dataset_id=dataset.id,
            timestamp_utc=earliest_ts,
            source_file_name=source_file_name,
        )
        session.add(run)
        session.flush()
    else:  # TODO: Will we re ingest a rundata or not
        # Update basic fields on re-ingestion
        run.agent_checksum = agent_checksum
        run.agent_cls_checksum = agent_cls_checksum
        run.dataset_id = dataset.id
        if source_file_name:
            run.source_file_name = source_file_name

        # Remove existing results for this run so we can replace them
        session.exec(delete(TaskResultDB).where(TaskResultDB.run_id == run.id))  # type: ignore[arg-type]

    # Aggregation accumulators
    total_tasks = 0
    success_count = 0
    failure_count = 0
    total_tokens = 0
    total_input_tokens = 0
    total_output_tokens = 0
    total_execution_time_sec = 0.0
    total_llm_invocation_count = 0

    # Collect run-level tags across all tasks (non-TASK_ prefixed)
    run_tag_pairs: set[tuple[str, str]] = set()

    # Insert TaskResultDB rows
    for tr in task_results:
        total_tasks += 1
        if tr.status == "Success":
            success_count += 1
        elif tr.status == "Failure":
            failure_count += 1

        # Ensure dataset and task exist
        # During ingestion, task_id is always a string (from JSONL)
        task = get_or_create_task(
            session, task_name=str(tr.task_id), kind=tr.task_kind, dataset=dataset
        )

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
            task_name=task.name,  # Store logical name for easier querying
            trace_id=tr.trace_id,
            timestamp_utc=ts_utc,
            status=tr.status,
            metrics=metrics_dict,
            failure_reason=tr.failure_reason,
            results=tr.results,
            task_metadata=metadata_dict,
        )
        session.add(run_result)

        # Process tags - separate TASK_ prefixed tags from run-level tags
        if tr.metadata and tr.metadata.tags:
            for key, value in tr.metadata.tags.items():
                if key.startswith(TASK_TAG_PREFIX):
                    # Task-level tag: strip prefix and link to task
                    task_tag_key = key[len(TASK_TAG_PREFIX) :]
                    tag = get_or_create_tag(session, key=task_tag_key, value=str(value))
                    link_tag_to_task(session, task, tag)
                else:
                    # Run-level tag
                    run_tag_pairs.add((key, str(value)))

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

    # Attach run-level tags (excluding TASK_ prefixed ones which were handled above)
    # First, clear existing links to avoid duplicates on re-ingestion
    session.exec(delete(RunTagLink).where(RunTagLink.run_id == run.id))  # type: ignore[arg-type]

    for key, value in sorted(run_tag_pairs):
        tag = get_or_create_tag(session, key=key, value=value)

        link_stmt = select(RunTagLink).where(
            RunTagLink.run_id == run.id,
            RunTagLink.tag_id == tag.id,
        )
        existing_link = session.exec(link_stmt).first()
        if existing_link is None:
            session.add(RunTagLink(run_id=run.id, tag_id=tag.id))

    return run


async def ingest_task_results(
    session: Session,
    task_results: Iterable[TaskResult],
    source_file_name: str | None = None,
) -> dict[str, int]:
    """
    Ingest an arbitrary collection of TaskResult entries which may span
    multiple runs and/or agent classes.

    Returns basic statistics about the ingestion.
    """
    # Group by run_id. Agent checksums are expected to be run-level invariants.
    grouped: dict[str, list[TaskResult]] = defaultdict(list)
    total_tasks = 0

    for tr in task_results:
        grouped[tr.run_id].append(tr)
        total_tasks += 1

    runs_ingested = 0
    for run_id, group in grouped.items():
        await ingest_task_results_for_run(
            session=session,
            run_id_str=run_id,
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
        .join(RunTagLink, RunTagLink.tag_id == Tag.id)  # type: ignore[arg-type]
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


def agent_class_exists(session: Session, cls_checksum: str) -> bool:
    """Return True if an agent class with the given checksum exists."""
    return (
        session.exec(
            select(AgentClassProvenance.cls_checksum).where(
                AgentClassProvenance.cls_checksum == cls_checksum
            )
        ).first()
        is not None
    )


def agent_instance_exists(session: Session, agent_checksum: str) -> bool:
    """Return True if an agent instance with the given checksum exists."""
    return (
        session.exec(
            select(AgentProvenance.agent_checksum).where(
                AgentProvenance.agent_checksum == agent_checksum
            )
        ).first()
        is not None
    )


def list_agents_from_db(session: Session) -> list[AgentClassSummary]:
    """
    List all agent classes with their total run counts and best run information.

    Uses the direct FK from Run.agent_cls_checksum to AgentClassProvenance.
    """
    # Load all runs joined directly with agent class provenance
    rows = session.exec(
        select(Run, AgentClassProvenance).join(
            AgentClassProvenance,
            cast(
                ColumnElement[bool],
                Run.agent_cls_checksum == AgentClassProvenance.cls_checksum,
            ),
        )
    ).all()

    # Group runs by agent class checksum
    grouped: dict[str, list[Run]] = {}
    agent_class_by_checksum: dict[str, AgentClassProvenance] = {}

    for run, agent_class in rows:
        agent_class_by_checksum[agent_class.cls_checksum] = agent_class
        grouped.setdefault(agent_class.cls_checksum, []).append(run)

    agent_summaries: list[AgentClassSummary] = []

    # Computing the Best Run for each agent class
    for cls_checksum, runs in sorted(grouped.items(), key=lambda x: x[0]):
        total_runs = len(runs)
        agent_class = agent_class_by_checksum[cls_checksum]

        # Prefer the run explicitly marked as best in the database, if any.
        # Fallback to the highest-scoring run if no flag is set.
        best_run_obj: Run | None = next((r for r in runs if r.is_best_run), None)
        if best_run_obj is None and runs:
            best_run_obj = max(runs, key=compute_score)

        best_run_info: RunInfo | None = None
        if best_run_obj is not None:
            best_run_tags = _get_tags_for_run(session, best_run_obj.id)
            best_run_dataset_name = _get_dataset_name_for_run(session, best_run_obj)
            # Get agent checksum from the run (runs belong to instances)
            agent_checksum = best_run_obj.agent_checksum

            best_run_info = RunInfo(
                run_id=str(best_run_obj.id),
                agent_cls_checksum=cls_checksum,
                agent_checksum=agent_checksum,
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

        agent_summaries.append(
            AgentClassSummary(
                cls_checksum=cls_checksum,
                cls_name=agent_class.cls_name,
                cls_provenance=agent_class.cls_provenance,
                total_runs=total_runs,
                best_run=best_run_info,
            )
        )

    return agent_summaries


def get_runs_by_agent_instance_from_db(
    session: Session, agent_checksum: str
) -> list[RunInfo]:
    """
    Get all runs for a specific agent instance, sorted by timestamp (most recent first).

    Args:
        agent_checksum: Checksum of the agent instance

    Returns:
        List of RunInfo objects for the specified agent instance
    """
    agent_instance = session.exec(
        select(AgentProvenance).where(AgentProvenance.agent_checksum == agent_checksum)
    ).first()
    if agent_instance is None:
        return []

    runs = session.exec(
        select(Run)
        .where(Run.agent_checksum == agent_checksum)
        .order_by(desc(Run.timestamp_utc))  # type: ignore[arg-type]  # type: ignore[arg-type]
    ).all()

    run_infos: list[RunInfo] = []

    for run in runs:
        run_tags = _get_tags_for_run(session, run.id)
        dataset_name = _get_dataset_name_for_run(session, run)

        run_infos.append(
            RunInfo(
                run_id=str(run.id),
                agent_cls_checksum=agent_instance.cls_checksum,
                agent_checksum=agent_checksum,
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


def get_runs_by_agent_from_db(
    session: Session, agent_cls_checksum: str
) -> list[RunInfo]:
    """
    Get all runs for a specific agent class, sorted by timestamp (most recent first).

    Uses the direct FK from Run.agent_cls_checksum to filter runs.
    """
    agent_class = session.exec(
        select(AgentClassProvenance).where(
            AgentClassProvenance.cls_checksum == agent_cls_checksum
        )
    ).first()
    if agent_class is None:
        return []

    # Get all runs directly by agent_cls_checksum
    runs = session.exec(
        select(Run)
        .where(cast(ColumnElement[bool], Run.agent_cls_checksum == agent_cls_checksum))
        .order_by(desc(Run.timestamp_utc))  # type: ignore[arg-type]
    ).all()

    run_infos: list[RunInfo] = []

    for run in runs:
        run_tags = _get_tags_for_run(session, run.id)
        dataset_name = _get_dataset_name_for_run(session, run)
        agent_checksum = run.agent_checksum

        run_infos.append(
            RunInfo(
                run_id=str(run.id),
                agent_cls_checksum=agent_cls_checksum,
                agent_checksum=agent_checksum,
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
    session: Session, agent_cls_checksum: str, dataset_id: str
) -> list[RunInfo] | None:
    """
    Get all runs for a specific agent class within a specific dataset, sorted by
    timestamp (most recent first).

    Uses the direct FK from Run.agent_cls_checksum to filter runs.
    """
    agent_class = session.exec(
        select(AgentClassProvenance).where(
            AgentClassProvenance.cls_checksum == agent_cls_checksum
        )
    ).first()
    if agent_class is None:
        # Agent class does not exist; let the caller decide how to handle this.
        return []

    dataset = session.exec(select(Dataset).where(Dataset.name == dataset_id)).first()
    if dataset is None:
        # Dataset does not exist; signal this with None so the caller can
        # distinguish it from "no runs yet".
        return None

    # Get all runs directly by agent_cls_checksum and dataset
    runs = session.exec(
        select(Run)
        .where(
            cast(ColumnElement[bool], Run.agent_cls_checksum == agent_cls_checksum),
            cast(ColumnElement[bool], Run.dataset_id == dataset.id),
        )
        .order_by(desc(Run.timestamp_utc))  # type: ignore[arg-type]
    ).all()

    run_infos: list[RunInfo] = []

    for run in runs:
        run_tags = _get_tags_for_run(session, run.id)
        dataset_name = _get_dataset_name_for_run(session, run)
        agent_checksum = run.agent_checksum

        run_infos.append(
            RunInfo(
                run_id=str(run.id),
                agent_cls_checksum=agent_cls_checksum,
                agent_checksum=agent_checksum,
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


def get_run_details_from_db(
    session: Session, run_ids: list[str]
) -> list[RunDetailsResponse]:
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

        agent_checksum = run.agent_checksum

        # Prefer the run-level class checksum (new schema); fall back to the
        # instance's cls_checksum for older runs.
        agent_instance = session.exec(
            select(AgentProvenance).where(
                AgentProvenance.agent_checksum == agent_checksum
            )
        ).first()
        agent_cls_checksum = run.agent_cls_checksum or (
            agent_instance.cls_checksum if agent_instance else ""
        )

        task_results_db = session.exec(
            select(TaskResultDB)
            .where(TaskResultDB.run_id == run.id)
            .order_by(TaskResultDB.timestamp_utc)  # type: ignore[arg-type]
        ).all()

        tasks: list[TaskResult] = []
        for tr_db in task_results_db:
            task = session.get(Task, tr_db.task_id)
            task_kind = (task.kind or "") if task else ""
            # Use stored task_name or fall back to task.name
            task_name = tr_db.task_name or (task.name if task else "")
            ground_truth = task.ground_truth if task else None
            # Get database task ID
            task_db_id = tr_db.task_id

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
                    task_id=task_db_id,  # Database integer ID
                    task_name=task_name,  # Logical task identifier string
                    ground_truth=ground_truth,
                    trace_id=tr_db.trace_id,
                    dataset_id=dataset_name,
                    timestamp_utc=tr_db.timestamp_utc.isoformat(),
                    agent_cls_checksum=agent_cls_checksum,
                    agent_checksum=agent_checksum,
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
                agent_cls_checksum=agent_cls_checksum,
                agent_checksum=agent_checksum,
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

    return TagsResponse(
        tags=tags_sorted, total_keys=total_keys, total_values=total_values
    )


def list_datasets_from_db(session: Session) -> list[DatasetInfo]:
    """
    List all datasets stored in the database.

    Returns them as DatasetInfo objects exposing the logical identifier
    (Dataset.name) as dataset_id.
    """
    datasets: Sequence[Dataset] = session.exec(
        select(Dataset).order_by(Dataset.name)
    ).all()

    result: list[DatasetInfo] = []
    for ds in datasets:
        created_at_str = (
            ds.created_at.isoformat() if ds.created_at is not None else None
        )
        result.append(
            DatasetInfo(
                dataset_id=ds.name,
                description=ds.description,
                created_at=created_at_str,
            )
        )
    return result


def get_instances_for_class_from_db(
    session: Session, cls_checksum: str
) -> list[AgentInstanceSummary] | None:
    """
    Get all agent instances for a specific agent class.

    Args:
        cls_checksum: The agent class checksum to filter by.

    Returns:
        List of AgentInstanceSummary objects for instances of that class,
        or None if the class does not exist.
    """
    # Check if the class exists
    agent_class = session.exec(
        select(AgentClassProvenance).where(
            AgentClassProvenance.cls_checksum == cls_checksum
        )
    ).first()
    if agent_class is None:
        return None

    # Get all instances for this class
    instances = session.exec(
        select(AgentProvenance).where(AgentProvenance.cls_checksum == cls_checksum)
    ).all()

    if not instances:
        return []

    # For each instance, get runs and compute best run
    instance_summaries: list[AgentInstanceSummary] = []

    for agent_instance in instances:
        runs = session.exec(
            select(Run).where(Run.agent_checksum == agent_instance.agent_checksum)
        ).all()

        total_runs = len(runs)

        # Find best run
        best_run_obj: Run | None = next((r for r in runs if r.is_best_run), None)
        if best_run_obj is None and runs:
            best_run_obj = max(runs, key=compute_score)

        best_run_info: RunInfo | None = None
        if best_run_obj is not None:
            best_run_tags = _get_tags_for_run(session, best_run_obj.id)
            best_run_dataset_name = _get_dataset_name_for_run(session, best_run_obj)

            best_run_info = RunInfo(
                run_id=str(best_run_obj.id),
                agent_cls_checksum=cls_checksum,
                agent_checksum=agent_instance.agent_checksum,
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

        instance_summaries.append(
            AgentInstanceSummary(
                agent_checksum=agent_instance.agent_checksum,
                cls_checksum=cls_checksum,
                name=agent_instance.name,
                provenance=agent_instance.provenance,
                total_runs=total_runs,
                best_run=best_run_info,
            )
        )

    return instance_summaries


def list_agent_instances_from_db(session: Session) -> list[AgentInstanceSummary]:
    """
    List all agent instances with their total run counts and best run information.

    Groups by agent_checksum and combines provenance with aggregate stats.
    """
    # Load all runs joined with agent instance provenance
    rows = session.exec(
        select(Run, AgentProvenance).join(
            AgentProvenance,
            cast(
                ColumnElement[bool],
                Run.agent_checksum == AgentProvenance.agent_checksum,
            ),
        )
    ).all()

    # Group runs by agent instance checksum
    grouped: dict[str, list[Run]] = {}
    agent_instance_by_checksum: dict[str, AgentProvenance] = {}

    for run, agent_instance in rows:
        agent_instance_by_checksum[agent_instance.agent_checksum] = agent_instance
        grouped.setdefault(agent_instance.agent_checksum, []).append(run)

    instance_summaries: list[AgentInstanceSummary] = []

    for agent_checksum, runs in sorted(grouped.items(), key=lambda x: x[0]):
        total_runs = len(runs)
        agent_instance = agent_instance_by_checksum[agent_checksum]

        # Prefer the run explicitly marked as best in the database, if any.
        # Fallback to the highest-scoring run if no flag is set.
        best_run_obj: Run | None = next((r for r in runs if r.is_best_run), None)
        if best_run_obj is None and runs:
            best_run_obj = max(runs, key=compute_score)

        best_run_info: RunInfo | None = None
        if best_run_obj is not None:
            best_run_tags = _get_tags_for_run(session, best_run_obj.id)
            best_run_dataset_name = _get_dataset_name_for_run(session, best_run_obj)
            agent_checksum_val = best_run_obj.agent_checksum

            best_run_info = RunInfo(
                run_id=str(best_run_obj.id),
                agent_cls_checksum=agent_instance.cls_checksum,
                agent_checksum=agent_checksum_val,
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

        instance_summaries.append(
            AgentInstanceSummary(
                agent_checksum=agent_checksum,
                cls_checksum=agent_instance.cls_checksum,
                name=agent_instance.name,
                provenance=agent_instance.provenance,
                total_runs=total_runs,
                best_run=best_run_info,
            )
        )

    return instance_summaries


def get_instances_for_class_in_dataset_from_db(
    session: Session, cls_checksum: str, dataset_id: str
) -> list[AgentInstanceSummary] | None:
    """
    Get all agent instances for a specific agent class within a specific dataset.

    Args:
        cls_checksum: The agent class checksum to filter by.
        dataset_id: The logical dataset identifier (e.g. "loop_corpus").

    Returns:
        List of AgentInstanceSummary objects for instances of that class in that dataset,
        or None if the dataset does not exist.
        Returns empty list if the class exists but has no instances with runs in this dataset.
    """
    # Check if the dataset exists
    dataset = session.exec(select(Dataset).where(Dataset.name == dataset_id)).first()
    if dataset is None:
        return None

    # Check if the class exists
    agent_class = session.exec(
        select(AgentClassProvenance).where(
            AgentClassProvenance.cls_checksum == cls_checksum
        )
    ).first()
    if agent_class is None:
        return []

    # Get all runs for instances of this class in this dataset
    rows = session.exec(
        select(Run, AgentProvenance)
        .join(
            AgentProvenance,
            cast(
                ColumnElement[bool],
                Run.agent_checksum == AgentProvenance.agent_checksum,
            ),
        )
        .where(
            cast(ColumnElement[bool], AgentProvenance.cls_checksum == cls_checksum),
            cast(ColumnElement[bool], Run.dataset_id == dataset.id),
        )
    ).all()

    if not rows:
        return []

    # Group runs by agent instance checksum
    grouped: dict[str, list[Run]] = {}
    agent_instance_by_checksum: dict[str, AgentProvenance] = {}

    for run, agent_instance in rows:
        agent_instance_by_checksum[agent_instance.agent_checksum] = agent_instance
        grouped.setdefault(agent_instance.agent_checksum, []).append(run)

    instance_summaries: list[AgentInstanceSummary] = []

    for agent_checksum, runs in sorted(grouped.items(), key=lambda x: x[0]):
        total_runs = len(runs)
        agent_instance = agent_instance_by_checksum[agent_checksum]

        # Find best run
        best_run_obj: Run | None = next((r for r in runs if r.is_best_run), None)
        if best_run_obj is None and runs:
            best_run_obj = max(runs, key=compute_score)

        best_run_info: RunInfo | None = None
        if best_run_obj is not None:
            best_run_tags = _get_tags_for_run(session, best_run_obj.id)
            best_run_dataset_name = _get_dataset_name_for_run(session, best_run_obj)

            best_run_info = RunInfo(
                run_id=str(best_run_obj.id),
                agent_cls_checksum=cls_checksum,
                agent_checksum=agent_checksum,
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

        instance_summaries.append(
            AgentInstanceSummary(
                agent_checksum=agent_checksum,
                cls_checksum=cls_checksum,
                name=agent_instance.name,
                provenance=agent_instance.provenance,
                total_runs=total_runs,
                best_run=best_run_info,
            )
        )

    return instance_summaries


def get_agents_for_dataset_from_db(
    session: Session, dataset_id: str
) -> list[AgentClassSummary] | None:
    """
    Get all agent classes that have at least one run for the given dataset.

    The dataset is identified by its logical identifier (Dataset.name), which
    corresponds to the JSONL `dataset_id` field (e.g. "loop_corpus").

    Uses the direct FK from Run.agent_cls_checksum to AgentClassProvenance.
    """
    dataset = session.exec(select(Dataset).where(Dataset.name == dataset_id)).first()
    if dataset is None:
        return None

    # Load all runs for this dataset joined directly with agent class provenance
    rows = session.exec(
        select(Run, AgentClassProvenance)
        .join(
            AgentClassProvenance,
            cast(
                ColumnElement[bool],
                Run.agent_cls_checksum == AgentClassProvenance.cls_checksum,
            ),
        )
        .where(cast(ColumnElement[bool], Run.dataset_id == dataset.id))
    ).all()

    if not rows:
        # Dataset exists but currently has no runs; return empty list.
        return []

    # Group runs by agent class checksum
    agents_runs: dict[str, list[Run]] = {}
    agent_class_by_checksum: dict[str, AgentClassProvenance] = {}
    for run, agent_class in rows:
        agents_runs.setdefault(agent_class.cls_checksum, []).append(run)
        agent_class_by_checksum[agent_class.cls_checksum] = agent_class

    agent_summaries: list[AgentClassSummary] = []

    for cls_checksum, runs in sorted(agents_runs.items(), key=lambda x: x[0]):
        agent_class = agent_class_by_checksum[cls_checksum]
        total_runs = len(runs)

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
            agent_checksum = best_run_obj.agent_checksum

            best_run_info = RunInfo(
                run_id=str(best_run_obj.id),
                agent_cls_checksum=cls_checksum,
                agent_checksum=agent_checksum,
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

        agent_summaries.append(
            AgentClassSummary(
                cls_checksum=cls_checksum,
                cls_name=agent_class.cls_name,
                cls_provenance=agent_class.cls_provenance,
                total_runs=total_runs,
                best_run=best_run_info,
            )
        )

    return agent_summaries


def get_agent_instances_for_dataset_from_db(
    session: Session, dataset_id: str
) -> list[AgentInstanceSummary] | None:
    """
    Get all agent instances that have at least one run for the given dataset.

    The dataset is identified by its logical `dataset_id` (e.g. "loop_corpus"),
    matching the `dataset_id` field in the ingested JSONL.
    """
    dataset = session.exec(select(Dataset).where(Dataset.name == dataset_id)).first()
    if dataset is None:
        return None

    # Load all runs for this dataset joined with agent instance provenance
    rows = session.exec(
        select(Run, AgentProvenance)
        .join(
            AgentProvenance,
            cast(
                ColumnElement[bool],
                Run.agent_checksum == AgentProvenance.agent_checksum,
            ),
        )
        .where(cast(ColumnElement[bool], Run.dataset_id == dataset.id))
    ).all()

    if not rows:
        # Dataset exists but currently has no runs; return empty list.
        return []

    # Group runs by agent instance checksum
    agents_runs: dict[str, list[Run]] = {}
    agent_instance_by_checksum: dict[str, AgentProvenance] = {}
    for run, agent_instance in rows:
        agents_runs.setdefault(agent_instance.agent_checksum, []).append(run)
        agent_instance_by_checksum[agent_instance.agent_checksum] = agent_instance

    instance_summaries: list[AgentInstanceSummary] = []

    for agent_checksum, runs in sorted(agents_runs.items(), key=lambda x: x[0]):
        agent_instance = agent_instance_by_checksum[agent_checksum]
        total_runs = len(runs)

        # Find best run
        best_run_obj: Run | None = next((r for r in runs if r.is_best_run), None)
        if best_run_obj is None and runs:
            best_run_obj = max(runs, key=compute_score)

        best_run_info: RunInfo | None = None
        if best_run_obj is not None:
            best_run_tags = _get_tags_for_run(session, best_run_obj.id)
            best_run_dataset_name = _get_dataset_name_for_run(session, best_run_obj)

            best_run_info = RunInfo(
                run_id=str(best_run_obj.id),
                agent_cls_checksum=agent_instance.cls_checksum,
                agent_checksum=agent_checksum,
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

        instance_summaries.append(
            AgentInstanceSummary(
                agent_checksum=agent_checksum,
                cls_checksum=agent_instance.cls_checksum,
                name=agent_instance.name,
                provenance=agent_instance.provenance,
                total_runs=total_runs,
                best_run=best_run_info,
            )
        )

    return instance_summaries


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


def get_agent_class_provenance_from_db(
    session: Session, cls_checksum: str
) -> AgentClassProvenance | None:
    """
    Fetch an AgentClassProvenance record by its checksum.

    Args:
        session: Database session.
        cls_checksum: The agent class checksum to look up.

    Returns:
        The AgentClassProvenance record if found, None otherwise.
    """
    return session.exec(
        select(AgentClassProvenance).where(
            AgentClassProvenance.cls_checksum == cls_checksum
        )
    ).first()


def get_agent_instance_provenance_from_db(
    session: Session, agent_checksum: str
) -> AgentProvenance | None:
    """
    Fetch an AgentProvenance (instance) record by its checksum.

    Args:
        session: Database session.
        agent_checksum: The agent instance checksum to look up.

    Returns:
        The AgentProvenance record if found, None otherwise.
    """
    return session.exec(
        select(AgentProvenance).where(AgentProvenance.agent_checksum == agent_checksum)
    ).first()


def get_runs_by_agent_instance_and_dataset_from_db(
    session: Session, agent_checksum: str, dataset_id: str
) -> list[RunInfo] | None:
    """
    Get all runs for a specific agent instance within a specific dataset,
    sorted by timestamp (most recent first).

    Args:
        session: Database session.
        agent_checksum: Checksum of the agent instance.
        dataset_id: Logical dataset identifier (e.g. "loop_corpus").

    Returns:
        List of RunInfo objects for the specified agent instance in the dataset,
        or None if the dataset does not exist.
    """
    agent_instance = session.exec(
        select(AgentProvenance).where(AgentProvenance.agent_checksum == agent_checksum)
    ).first()

    if agent_instance is None:
        return []

    dataset = session.exec(select(Dataset).where(Dataset.name == dataset_id)).first()

    if dataset is None:
        # Dataset does not exist; signal this with None so the caller can
        # distinguish it from "no runs yet".
        return None

    runs = session.exec(
        select(Run)
        .where(Run.agent_checksum == agent_checksum, Run.dataset_id == dataset.id)
        .order_by(desc(Run.timestamp_utc))  # type: ignore[arg-type]
    ).all()

    run_infos: list[RunInfo] = []

    for run in runs:
        run_tags = _get_tags_for_run(session, run.id)
        dataset_name = _get_dataset_name_for_run(session, run)

        run_infos.append(
            RunInfo(
                run_id=str(run.id),
                agent_cls_checksum=agent_instance.cls_checksum,
                agent_checksum=agent_checksum,
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


def get_task_name_from_db(session: Session, task_id: int) -> str | None:
    """
    Get the task name (logical identifier) from the database given the task ID.

    Args:
        session: Database session.
        task_id: The database task ID (integer).

    Returns:
        The task name string, or None if not found.
    """
    task = session.get(Task, task_id)
    if task is None:
        return None
    return task.name


def get_estimated_time_for_task_from_db(
    session: Session, run_id: str, task_id: int
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


# ============================================================================
# Dataset Tasks API Functions
# ============================================================================


def get_tasks_for_dataset_from_db(
    session: Session, dataset_id: str
) -> DatasetTasksResponse | None:
    """
    Get all tasks in a specific dataset with their tags.

    Args:
        dataset_id: Logical dataset identifier (e.g. "loop_corpus").

    Returns:
        DatasetTasksResponse containing all tasks in the dataset,
        or None if the dataset does not exist.
    """
    dataset = session.exec(select(Dataset).where(Dataset.name == dataset_id)).first()
    if dataset is None:
        return None

    # Get all tasks for this dataset
    tasks_db = session.exec(
        select(Task).where(Task.dataset_id == dataset.id).order_by(Task.name)
    ).all()

    task_infos: list[TaskInfo] = []
    for task in tasks_db:
        # Get tags for this task
        task_tags = get_tags_for_task(session, task.id) if task.id else {}

        task_infos.append(
            TaskInfo(
                task_id=task.id or 0,
                task_name=task.name,
                task_kind=task.kind,
                dataset_id=dataset_id,
                tags=task_tags,
            )
        )

    return DatasetTasksResponse(
        dataset_id=dataset_id,
        tasks=task_infos,
        total_tasks=len(task_infos),
    )


def get_task_details_from_db(
    session: Session, task_id: int
) -> TaskDetailsResponse | None:
    """
    Get a single task's details including tags and dataset info.

    Args:
        task_id: The database task ID (integer).

    Returns:
        TaskDetailsResponse with task details, or None if not found.
    """
    task = session.get(Task, task_id)
    if task is None:
        return None

    dataset_name: str | None = None
    dataset_info: DatasetInfo | None = None
    if task.dataset_id is not None:
        dataset = session.get(Dataset, task.dataset_id)
        if dataset is not None:
            dataset_name = dataset.name
            created_at_str = (
                dataset.created_at.isoformat()
                if dataset.created_at is not None
                else None
            )
            dataset_info = DatasetInfo(
                dataset_id=dataset.name,
                description=dataset.description,
                created_at=created_at_str,
            )

    task_tags = get_tags_for_task(session, task_id)

    return TaskDetailsResponse(
        task_id=task.id or 0,
        task_name=task.name,
        task_kind=task.kind,
        dataset_id=dataset_name,
        dataset=dataset_info,
        ground_truth=task.ground_truth,
        tags=task_tags,
    )


def get_dataset_results_from_db(
    session: Session, dataset_id: str
) -> DatasetResultsResponse | None:
    """
    Get the complete results matrix for a dataset.

    This is the main API for the dataset details page, showing task results
    across all agent instances.

    Args:
        dataset_id: Logical dataset identifier (e.g. "loop_corpus").

    Returns:
        DatasetResultsResponse containing:
        - All tasks in the dataset with their tags
        - All agent instances that have runs on this dataset
        - Result matrix with success/total counts per (task, agent_instance)

        Returns None if the dataset does not exist.
    """
    dataset = session.exec(select(Dataset).where(Dataset.name == dataset_id)).first()
    if dataset is None:
        return None

    # Get all tasks for this dataset
    tasks_db = session.exec(
        select(Task).where(Task.dataset_id == dataset.id).order_by(Task.name)
    ).all()

    # Build task info list with tags
    tasks_list: list[DatasetResultsTask] = []
    task_id_map: dict[int, DatasetResultsTask] = {}  # Map DB ID to task info
    for task in tasks_db:
        if task.id is None:
            continue
        task_tags = get_tags_for_task(session, task.id)
        task_info = DatasetResultsTask(
            task_id=task.id,
            task_name=task.name,
            task_kind=task.kind,
            dataset_id=dataset_id,
            tags=task_tags,
        )
        tasks_list.append(task_info)
        task_id_map[task.id] = task_info

    # Get all runs for this dataset with their agent instances and class info
    rows = session.exec(
        select(Run, AgentProvenance, AgentClassProvenance)
        .join(
            AgentProvenance,
            cast(
                ColumnElement[bool],
                Run.agent_checksum == AgentProvenance.agent_checksum,
            ),
        )
        .join(
            AgentClassProvenance,
            cast(
                ColumnElement[bool],
                AgentProvenance.cls_checksum == AgentClassProvenance.cls_checksum,
            ),
        )
        .where(cast(ColumnElement[bool], Run.dataset_id == dataset.id))
        .order_by(desc(Run.timestamp_utc))  # type: ignore[arg-type]
    ).all()

    # Build unique agent instances list with all their run IDs
    # Use a dict to track unique agent checksums, their info, and all run IDs
    agent_instance_map: dict[
        str, tuple[AgentProvenance, AgentClassProvenance, list[str]]
    ] = {}
    for run, agent_instance, agent_class in rows:
        if agent_instance.agent_checksum not in agent_instance_map:
            agent_instance_map[agent_instance.agent_checksum] = (
                agent_instance,
                agent_class,
                [str(run.id)],
            )
        else:
            # Append run ID to the list
            agent_instance_map[agent_instance.agent_checksum][2].append(str(run.id))

    agent_instances_list: list[DatasetResultsAgentInstance] = []
    for agent_checksum, (agent_instance, agent_class, run_ids) in sorted(
        agent_instance_map.items(), key=lambda x: x[1][0].name
    ):
        agent_instances_list.append(
            DatasetResultsAgentInstance(
                agent_instance_id=agent_checksum,
                agent_name=agent_instance.name,
                agent_checksum=agent_checksum,
                agent_cls_checksum=agent_class.cls_checksum,
                agent_cls_name=agent_class.cls_name,
                provenance={
                    "agent_instance": agent_instance.provenance,
                    "agent_class": agent_class.cls_provenance,
                },
                run_ids=run_ids,
            )
        )

    # Build results matrix: aggregate success/total counts per (task, agent_instance)
    # across all runs
    results_map: dict[tuple[int, str], dict[str, int]] = {}

    # Get all task results for tasks in this dataset
    # We filter by joining with Task to get only results for tasks in this dataset
    task_ids_in_dataset = list(task_id_map.keys())
    if task_ids_in_dataset:
        task_results = session.exec(
            select(TaskResultDB).where(
                TaskResultDB.task_id.in_(task_ids_in_dataset)  # type: ignore[attr-defined]
            )
        ).all()
    else:
        task_results = []

    for tr in task_results:
        # Get the run to find the agent instance
        run_obj = session.get(Run, tr.run_id)
        if run_obj is None:
            continue

        agent_checksum = run_obj.agent_checksum
        task_id = tr.task_id

        key = (task_id, agent_checksum)
        if key not in results_map:
            results_map[key] = {"success_count": 0, "total_count": 0}

        results_map[key]["total_count"] += 1
        if tr.status == "Success":
            results_map[key]["success_count"] += 1

    # Convert to list of DatasetTaskResult
    results_list: list[DatasetTaskResult] = []
    for (task_id, agent_checksum), counts in sorted(results_map.items()):
        results_list.append(
            DatasetTaskResult(
                task_id=task_id,
                agent_instance_id=agent_checksum,
                success_count=counts["success_count"],
                total_count=counts["total_count"],
            )
        )

    return DatasetResultsResponse(
        dataset_id=dataset_id,
        tasks=tasks_list,
        agent_instances=agent_instances_list,
        results=results_list,
    )


def get_task_result_from_db(
    session: Session, run_id: str, task_id: int
) -> TaskResult | None:
    """
    Get the complete task result info for a specific run and task.

    Args:
        run_id: The run UUID as a string.
        task_id: The database task ID (integer).

    Returns:
        TaskResult with complete info, or None if not found.
    """
    try:
        run_uuid = UUID(run_id)
    except ValueError:
        logger.warning(
            "get_task_result_from_db: Invalid run_id format '%s' (not a valid UUID)",
            run_id,
        )
        return None

    # Query the task result
    tr_db = session.exec(
        select(TaskResultDB).where(
            TaskResultDB.run_id == run_uuid,
            TaskResultDB.task_id == task_id,
        )
    ).first()

    if tr_db is None:
        logger.warning(
            "get_task_result_from_db: No TaskResult found for run_id='%s', task_id=%d",
            run_id,
            task_id,
        )
        return None

    # Get related entities
    run = session.get(Run, run_uuid)
    if run is None:
        logger.warning(
            "get_task_result_from_db: Run not found for run_id='%s'",
            run_id,
        )
        return None

    task = session.get(Task, task_id)
    if task is None:
        logger.warning(
            "get_task_result_from_db: Task not found for task_id=%d",
            task_id,
        )
        return None

    # Get agent info
    agent_checksum = run.agent_checksum
    agent_cls_checksum = run.agent_cls_checksum or ""

    # Get dataset name
    dataset_name: str | None = None
    if task.dataset_id is not None:
        ds = session.get(Dataset, task.dataset_id)
        if ds is not None:
            dataset_name = ds.name

    # Build the response
    task_kind = task.kind or ""
    task_name = tr_db.task_name or task.name

    if tr_db.metrics is None:
        logger.warning(
            "get_task_result_from_db: TaskResult has no metrics for run_id='%s', task_id=%d",
            run_id,
            task_id,
        )
        return None

    metrics = Metrics.model_validate(tr_db.metrics)
    metadata = (
        TaskMetadata.model_validate(tr_db.task_metadata)
        if tr_db.task_metadata is not None
        else TaskMetadata()
    )

    return TaskResult(
        run_id=str(run.id),
        task_kind=task_kind,
        task_id=task_id,
        task_name=task_name,
        trace_id=tr_db.trace_id,
        dataset_id=dataset_name,
        ground_truth=task.ground_truth,
        timestamp_utc=tr_db.timestamp_utc.isoformat(),
        agent_cls_checksum=agent_cls_checksum,
        agent_checksum=agent_checksum,
        status=tr_db.status,
        metrics=metrics,
        metadata=metadata,
        results=tr_db.results,
        failure_reason=tr_db.failure_reason,
    )


def bulk_add_tags_to_tasks(
    session: Session,
    task_ids: list[int],
    tags: list[str],
) -> BulkAddTagsResponse:
    """
    Add multiple tags to multiple tasks.

    Args:
        session: Database session.
        task_ids: List of task database IDs to add tags to.
        tags: List of tag strings (each string is used as both key and value).

    Returns:
        BulkAddTagsResponse with success status and counts.
    """
    if not task_ids:
        return BulkAddTagsResponse(
            success=True,
            message="No task IDs provided",
            tasks_updated=0,
            tags_added=0,
        )

    if not tags:
        return BulkAddTagsResponse(
            success=True,
            message="No tags provided",
            tasks_updated=0,
            tags_added=0,
        )

    # Verify all tasks exist
    existing_tasks = session.exec(
        select(Task).where(
            cast(ColumnElement[bool], Task.id.in_(task_ids))  # type: ignore[union-attr]
        )
    ).all()

    existing_task_ids = {task.id for task in existing_tasks if task.id is not None}
    missing_task_ids = set(task_ids) - existing_task_ids

    if missing_task_ids:
        return BulkAddTagsResponse(
            success=False,
            message=f"Tasks not found: {sorted(missing_task_ids)}",
            tasks_updated=0,
            tags_added=0,
        )

    # Add tags to each task
    total_tags_added = 0
    tasks_updated = 0

    for task in existing_tasks:
        if task.id is None:
            continue

        task_had_new_tags = False
        for tag_str in tags:
            # Get or create the tag (use same string for key and value)
            tag = get_or_create_tag(session, key=tag_str, value=tag_str)

            # Check if link already exists
            existing_link = session.exec(
                select(TaskTagLink).where(
                    TaskTagLink.task_id == task.id,
                    TaskTagLink.tag_id == tag.id,
                )
            ).first()

            if existing_link is None:
                # Create the link
                session.add(TaskTagLink(task_id=task.id, tag_id=tag.id))
                total_tags_added += 1
                task_had_new_tags = True

        if task_had_new_tags:
            tasks_updated += 1

    session.flush()

    return BulkAddTagsResponse(
        success=True,
        message=f"Added {total_tags_added} tag(s) to {tasks_updated} task(s)",
        tasks_updated=tasks_updated,
        tags_added=total_tags_added,
    )


def get_runs_for_agent_and_task_from_db(
    session: Session, agent_checksum: str, task_id: int
) -> AgentTaskRunsResponse | None:
    """
    Get all run IDs for a specific agent instance on a specific task.

    Args:
        session: Database session.
        agent_checksum: The agent instance checksum.
        task_id: The database task ID (integer).

    Returns:
        AgentTaskRunsResponse containing the list of run IDs,
        or None if the task does not exist.
    """
    # Check if the task exists
    task = session.get(Task, task_id)
    if task is None:
        return None

    # Get all task results for this agent and task
    # Join TaskResultDB with Run to filter by agent_checksum
    rows = session.exec(
        select(TaskResultDB, Run)
        .join(
            Run,
            cast(ColumnElement[bool], TaskResultDB.run_id == Run.id),
        )
        .where(
            cast(ColumnElement[bool], TaskResultDB.task_id == task_id),
            cast(ColumnElement[bool], Run.agent_checksum == agent_checksum),
        )
        .order_by(desc(Run.timestamp_utc))  # type: ignore[arg-type]
    ).all()

    run_ids: list[str] = []
    seen_run_ids: set[str] = set()
    for _task_result, run in rows:
        run_id_str = str(run.id)
        if run_id_str not in seen_run_ids:
            run_ids.append(run_id_str)
            seen_run_ids.add(run_id_str)

    return AgentTaskRunsResponse(
        agent_checksum=agent_checksum,
        task_id=task_id,
        task_name=task.name,
        run_ids=run_ids,
        total_runs=len(run_ids),
    )
