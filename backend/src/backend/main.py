"""
FastAPI backend server for Rocq_agent task results.

This service exposes a read/write API backed by a PostgreSQL database.
Task results are ingested via the `/api/ingest` endpoint and normalised
into a relational schema for querying and dashboard use.
"""
# ruff: noqa: B008
import logging
from collections.abc import AsyncGenerator
from contextlib import asynccontextmanager
from typing import Any

import uvicorn
from fastapi import Body, Depends, FastAPI, File, HTTPException, Query, UploadFile
from fastapi.middleware.cors import CORSMiddleware
from sqlmodel import Session

from backend.config import settings
from backend.dal import (
    agent_exists,
    get_agents_for_dataset_from_db,
    get_estimated_time_for_task_from_db,
    get_run_details_from_db,
    get_runs_by_agent_and_dataset_from_db,
    get_runs_by_agent_from_db,
    get_unique_tags_from_db,
    ingest_task_results,
    list_agents_from_db,
    list_datasets_from_db,
    set_best_run_flag_for_run,
)
from backend.database import get_session, init_db
from backend.models import (
    AgentInfo,
    BestRunUpdateResponse,
    DatasetAgentsResponse,
    DatasetInfo,
    IngestionResponse,
    ObservabilityLabelsResponse,
    ObservabilityLogsResponse,
    RunDetailsResponse,
    RunInfo,
    TagsResponse,
    TaskResult,
)
from backend.utils import fetch_observability_logs, get_labels_grouped_by_log

# Configure logging
logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s"
)
logger = logging.getLogger(__name__)


@asynccontextmanager
async def lifespan(app: FastAPI) -> AsyncGenerator[Any]:
    """
    Lifespan context manager for startup and shutdown events.

    On startup, this initialises the database schema (creating tables if
    they do not already exist). No data is loaded from disk; all state
    is stored in the database.
    """
    logger.info("Starting FastAPI backend...")

    # Initialize database schema
    try:
        logger.info("Initializing database schema...")
        init_db()
        logger.info("Database schema initialized successfully.")
    except Exception as e:  # pragma: no cover - defensive logging
        logger.error("Failed to initialize database schema: %s", e, exc_info=True)


    yield

    logger.info("Shutting down FastAPI backend...")


# Create FastAPI application
app = FastAPI(
    title="Rocq Agent Toolkit Backend",
    description="Backend API for Rocq_agent task results",
    version="1.0.0",
    lifespan=lifespan,
)

# Configure CORS for frontend access
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],  # In production, specify exact origins
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)


@app.get("/")
async def root() -> dict[str, str]:
    """Root endpoint - health check."""
    return {
        "message": "Rocq Agent Toolkit Backend API",
        "version": "1.0.0",
        "status": "running",
    }


@app.get("/api/health")
async def health_check(session: Session = Depends(get_session)) -> dict[str, Any]:
    """
    Health check endpoint.

    Returns:
        System status information
    """
    total_agents = len(list_agents_from_db(session))
    return {
        "status": "healthy",
        "total_agents": total_agents or 0,
        "config": {
            "observability_url": settings.observability_url,
            "Database URL": f"{settings.postgres_host}:{settings.postgres_port}",
        },
    }


def _perform_ingestion(
    *,
    session: Session,
    task_results: list[TaskResult],
    source_file_name: str | None,
) -> IngestionResponse:
    """
    Common ingestion logic used by both the JSON and file-based endpoints.
    """
    if not task_results:
        raise HTTPException(
            status_code=400,
            detail="No task results provided. Supply at least one TaskResult.",
        )

    try:
        stats = ingest_task_results(
            session=session,
            task_results=task_results,
            source_file_name=source_file_name,
        )
        session.commit()
    except HTTPException:
        # Bubble up HTTPExceptions unchanged
        raise
    except Exception as e:  # pragma: no cover - defensive logging
        session.rollback()
        logger.error("Error ingesting task results: %s", e, exc_info=True)
        raise HTTPException(
            status_code=500,
            detail=f"Error ingesting task results: {str(e)}",
        ) from e

    message = (
        f"Ingested {stats['tasks_ingested']} task results "
        f"across {stats['runs_ingested']} runs."
    )

    return IngestionResponse(
        success=True,
        message=message,
        runs_ingested=stats["runs_ingested"],
        tasks_ingested=stats["tasks_ingested"],
    )


@app.post("/api/ingest", response_model=IngestionResponse)
async def ingest_items(
    items: list[TaskResult] = Body(
        ...,
        description="JSON array of task result objects matching the TaskResult schema",
    ),
    source_file_name: str = Query(
        description=(
            "Source file name for the task results"
        ),
    ),
    session: Session = Depends(get_session),
) -> IngestionResponse:
    """
    Ingest task results provided as a JSON array in the request body.

    This endpoint expects the request body to be a JSON array of `TaskResult`
    objects. It does not support file uploads.
    """
    return _perform_ingestion(
        session=session,
        task_results=items,
        source_file_name=source_file_name,
    )


@app.post("/api/ingest/file", response_model=IngestionResponse)
async def ingest_jsonl_file(
    file: UploadFile = File(
        ...,
        description="JSONL file where each line is a JSON object matching `TaskResult`",
    ),
    source_file_name: str | None = Query(
        default=None,
        description="Optional source file name for the task results; defaults to the uploaded file name",
    ),
    session: Session = Depends(get_session),
) -> IngestionResponse:
    """
    Ingest task results from a JSONL file upload.

    Each non-empty line in the uploaded file must be a JSON object matching
    the `TaskResult` schema. Invalid lines are logged and skipped.
    """
    if not source_file_name:
        source_file_name = file.filename

    raw_bytes = await file.read()
    text = raw_bytes.decode("utf-8")
    parsed_items: list[TaskResult] = []
    parse_error_count = 0

    for line_number, line in enumerate(text.splitlines(), start=1):
        line = line.strip()
        if not line:
            continue
        try:
            # Let Pydantic handle the JSON parsing & validation
            parsed_items.append(TaskResult.model_validate_json(line))
        except Exception as e:  # pragma: no cover - validation guard rail
            # Log and skip invalid JSONL entries instead of failing the entire request,
            # mirroring the behaviour of the previous file-based loader.
            parse_error_count += 1
            logger.warning(
                "Skipping invalid JSONL entry in %s at line %d: %s",
                source_file_name or "<upload>",
                line_number,
                e,
            )

    if parse_error_count:
        logger.info(
            "Completed ingestion with %d invalid JSONL lines skipped for file %s",
            parse_error_count,
            source_file_name or "<upload>",
        )

    return _perform_ingestion(
        session=session,
        task_results=parsed_items,
        source_file_name=source_file_name,
    )



@app.get("/api/agents", response_model=list[AgentInfo])
async def list_agents(session: Session = Depends(get_session)) -> list[AgentInfo]:
    """
    List all unique agents that have been ingested into the database.

    Returns:
        List of AgentInfo objects containing agent names and run counts
    """
    try:
        agents = list_agents_from_db(session)
        return agents
    except Exception as e:
        logger.error(f"Error fetching agents: {e}")
        raise HTTPException(
            status_code=500, detail=f"Error fetching agents: {str(e)}"
        ) from e


@app.get("/api/agents/{agent_name}/runs", response_model=list[RunInfo])
async def list_runs_by_agent(
    agent_name: str, session: Session = Depends(get_session)
) -> list[RunInfo]:
    """
    List all runs for a specific agent.

    Args:
        agent_name: Name of the agent

    Returns:
        List of RunInfo objects for the specified agent
    """
    try:
        runs = get_runs_by_agent_from_db(session, agent_name)

        if not runs and not agent_exists(session, agent_name):
            raise HTTPException(
                status_code=404, detail=f"Agent '{agent_name}' not found"
            )

        return runs
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Error fetching runs for agent '{agent_name}': {e}")
        raise HTTPException(
            status_code=500, detail=f"Error fetching runs: {str(e)}"
        ) from e


@app.get(
    "/api/{dataset_id}/agents/{agent_name}/runs",
    response_model=list[RunInfo],
)
async def list_runs_by_agent_for_dataset(
    dataset_id: str,
    agent_name: str,
    session: Session = Depends(get_session),
) -> list[RunInfo]:
    """
    List all runs for a specific agent within a specific dataset.

    Args:
        dataset_id: Logical dataset identifier (e.g. "function_corpus")
        agent_name: Name of the agent

    Returns:
        List of RunInfo objects for the specified agent and dataset.
    """
    try:
        runs = get_runs_by_agent_and_dataset_from_db(session, agent_name, dataset_id)

        if runs is None:
            # Dataset not found
            raise HTTPException(
                status_code=404, detail=f"Dataset '{dataset_id}' not found"
            )

        if not runs and not agent_exists(session, agent_name):
            raise HTTPException(
                status_code=404, detail=f"Agent '{agent_name}' not found"
            )

        return runs
    except HTTPException:
        raise
    except Exception as e:
        logger.error(
            "Error fetching runs for agent '%s' in dataset '%s': %s",
            agent_name,
            dataset_id,
            e,
        )
        raise HTTPException(
            status_code=500,
            detail=(
                f"Error fetching runs for agent '{agent_name}' "
                f"in dataset '{dataset_id}': {str(e)}"
            ),
        ) from e


@app.get("/api/runs/details", response_model=list[RunDetailsResponse])
async def get_run_details(
    run_ids: str = Query(..., description="Comma-separated list of run IDs to retrieve"),
    session: Session = Depends(get_session),
) -> list[RunDetailsResponse]:
    """
    Get complete details for one or more runs.

    Args:
        run_ids: Comma-separated list of run IDs

    Returns:
        List of RunDetailsResponse objects containing all tasks for each run

    Example:
        /api/runs/details?run_ids=abc123,def456,ghi789
    """
    # Split and clean the IDs
    id_list = [rid.strip() for rid in run_ids.split(",") if rid.strip()]

    if not id_list:
        raise HTTPException(
            status_code=400, detail="At least one run_id must be provided"
        )

    try:
        results = get_run_details_from_db(session, id_list)

        if not results:
            raise HTTPException(
                status_code=404, detail="No runs found for the provided run_ids"
            )

        return results
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Error fetching run details: {e}")
        raise HTTPException(
            status_code=500, detail=f"Error fetching run details: {str(e)}"
        ) from e


@app.post("/api/runs/{run_id}/best-run", response_model=BestRunUpdateResponse)
async def update_best_run_flag(
    run_id: str,
    best_run: bool = Query(
        ...,
        description=(
            "Boolean flag indicating whether this run should be marked as the best run "
            "for its agent (true) or unmarked (false)."
        ),
    ),
    session: Session = Depends(get_session),
) -> BestRunUpdateResponse:
    """
    Set or unset the 'best run' flag for a specific run.

    This endpoint toggles the underlying `is_best_run` boolean field on the Run
    row identified by `run_id` and returns the updated RunInfo view.
    """
    try:
        updated_flag = set_best_run_flag_for_run(
            session=session,
            run_id=run_id,
            best_run=best_run,
        )
        session.commit()
        return BestRunUpdateResponse(run_id=run_id, best_run=updated_flag)
    except LookupError as e:
        session.rollback()
        raise HTTPException(status_code=404, detail=str(e)) from e
    except ValueError as e:
        session.rollback()
        raise HTTPException(status_code=400, detail=str(e)) from e
    except Exception as e:
        session.rollback()
        logger.error(
            "Error updating best_run flag for run '%s': %s", run_id, e, exc_info=True
        )
        raise HTTPException(
            status_code=500,
            detail=f"Error updating best_run flag for run '{run_id}': {str(e)}",
        ) from e


@app.get("/api/tags", response_model=TagsResponse)
async def list_tags(session: Session = Depends(get_session)) -> TagsResponse:
    """
    List all unique metadata tags across all runs/tasks stored in the database.

    Returns:
        TagsResponse containing tag keys and their unique values.
    """
    try:
        tags_response = get_unique_tags_from_db(session)
        return tags_response
    except Exception as e:
        logger.error(f"Error fetching tags: {e}", exc_info=True)
        raise HTTPException(
            status_code=500, detail=f"Error fetching tags: {str(e)}"
        ) from e


@app.get("/api/datasets", response_model=list[DatasetInfo])
async def list_datasets(session: Session = Depends(get_session)) -> list[DatasetInfo]:
    """
    List all datasets that have been created in the database.

    Each dataset is identified by its logical `dataset_id` (e.g. "loop_corpus")
    which corresponds to the JSONL field, along with optional description and
    creation time.
    """
    try:
        return list_datasets_from_db(session)
    except Exception as e:
        logger.error("Error fetching datasets: %s", e, exc_info=True)
        raise HTTPException(
            status_code=500, detail=f"Error fetching datasets: {str(e)}"
        ) from e


@app.get(
    "/api/{dataset_id}/agents",
    response_model=DatasetAgentsResponse,
)
async def list_agents_for_dataset(
    dataset_id: str, session: Session = Depends(get_session)
) -> DatasetAgentsResponse:
    """
    List all agents that have at least one run for the given dataset.

    The dataset is identified by its logical `dataset_id` (e.g. "loop_corpus"),
    matching the `dataset_id` field in the ingested JSONL.
    """
    try:
        result = get_agents_for_dataset_from_db(session, dataset_id)
        if result is None:
            raise HTTPException(
                status_code=404,
                detail=f"Dataset '{dataset_id}' not found",
            )
        return result
    except HTTPException:
        raise
    except Exception as e:
        logger.error(
            "Error fetching agents for dataset '%s': %s", dataset_id, e, exc_info=True
        )
        raise HTTPException(
            status_code=500,
            detail=f"Error fetching agents for dataset '{dataset_id}': {str(e)}",
        ) from e



@app.get("/api/observability/logs/raw", response_model=ObservabilityLogsResponse)
async def get_observability_logs_raw(
    run_id: str = Query(..., description="Run ID to fetch logs for"),
    task_id: str = Query(..., description="Task ID to fetch logs for"),
    session: Session = Depends(get_session),
) -> ObservabilityLogsResponse:
    """
    Fetch raw observability logs from Loki for a specific run and task.

    Queries the Loki instance configured in settings to retrieve logs filtered by:
    - service_name: "Rocq_agent"
    - run_id: provided run ID
    - task_id: provided task ID

    Returns the raw log entries (after basic label filtering), without
    any aggregation or additional post-processing.

    Args:
        run_id: The run ID to filter logs by
        task_id: The task ID to filter logs by

    Returns:
        ObservabilityLogsResponse containing unique label key-value pairs

    Example:
        /api/observability/logs/raw?run_id=abc123&task_id=task456
    """
    try:
        estimated_time = get_estimated_time_for_task_from_db(session, run_id, task_id)
        logs = await fetch_observability_logs(
            run_id=run_id, task_id=task_id, estimated_time=estimated_time
        )

        logger.info(f"Retrieved {len(logs)} log entries from Loki (raw endpoint)")

        return ObservabilityLogsResponse(
            run_id=run_id,
            task_id=task_id,
            logs=logs,
            total_logs=len(logs),
        )
    except Exception as e:
        logger.error(
            f"Error fetching raw observability logs: {e}", exc_info=True
        )
        raise HTTPException(
            status_code=500, detail=f"Error fetching raw logs: {str(e)}"
        ) from e




@app.get("/api/observability/logs", response_model=ObservabilityLabelsResponse)
async def get_observability_logs(
    run_id: str = Query(..., description="Run ID to fetch logs for"),
    task_id: str = Query(..., description="Task ID to fetch logs for"),
    session: Session = Depends(get_session),
) -> ObservabilityLabelsResponse:
    """
    Fetch observability log labels from Loki for a specific run and task.

    This endpoint uses the shared utility function in `utils.py` to fetch
    raw logs from Loki, then performs postprocessing to aggregate labels.

    Returns only the unique labels from the logs after filtering.

    Example:
        /api/observability/logs?run_id=abc123&task_id=task456
    """
    try:
        # Fetch raw logs via shared utility, using DB-backed estimated time
        estimated_time = get_estimated_time_for_task_from_db(session, run_id, task_id)
        logs = await fetch_observability_logs(
            run_id=run_id, task_id=task_id, estimated_time=estimated_time
        )

        logger.info(f"Retrieved {len(logs)} log entries from Loki")

        # Extract unique labels from the logs (filter already applied)
        labels_dict = get_labels_grouped_by_log(logs, marker="status", group_name="tactic")

        logger.info(f"Extracted {len(labels_dict)} unique labels from logs")

        return ObservabilityLabelsResponse(
            run_id=run_id,
            task_id=task_id,
            labels=labels_dict,
            total_labels=len(labels_dict),
        )
    except HTTPException:
        # Let HTTPExceptions from the utility bubble up unchanged
        raise
    except Exception as e:
        logger.error(
            f"Error fetching observability log labels: {e}", exc_info=True
        )
        raise HTTPException(
            status_code=500, detail=f"Error fetching log labels: {str(e)}"
        ) from e


if __name__ == "__main__":

    uvicorn.run(
        "main:app",
        host=settings.server_host,
        port=settings.server_port,
        reload=True,
        log_level=settings.log_level,
    )
