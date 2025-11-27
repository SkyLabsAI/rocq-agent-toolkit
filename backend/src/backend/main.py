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
    get_estimated_time_for_task_from_db,
    get_run_details_from_db,
    get_runs_by_agent_from_db,
    get_unique_tags_from_db,
    ingest_task_results,
    list_agents_from_db,
)
from backend.database import get_session, init_db
from backend.models import (
    AgentInfo,
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


@app.post("/api/ingest", response_model=IngestionResponse)
async def ingest_jsonl(
    file: UploadFile | None = File(
        default=None, description="Optional JSONL file containing task results"
    ),
    items: list[TaskResult] | None = Body(
        default=None,
        description="Optional list of task result JSON objects matching the TaskResult schema",
    ),
    source_file_name: str | None = Query(
        default=None,
        description="Optional source file name for the task results, when providing list of tasks",
    ),
    session: Session = Depends(get_session),
) -> IngestionResponse:
    """
    Ingest task results into the database.

    This endpoint accepts either:
    - A JSONL file upload where each line is a JSON object matching `TaskResult`
    - A JSON array of `TaskResult` objects in the request body

    All ingested data is normalised into the relational schema and run-level
    aggregates are computed for each run.
    """
    parsed_items: list[TaskResult] = []

    if file is not None:
        if not source_file_name:
            source_file_name = file.filename
        raw_bytes = await file.read()
        text = raw_bytes.decode("utf-8")
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

    if items:
        parsed_items.extend(items)

    if not parsed_items:
        raise HTTPException(
            status_code=400,
            detail="No task results provided. Supply a JSONL file or a non-empty list of items.",
        )

    try:
        stats = ingest_task_results(
            session=session,
            task_results=parsed_items,
            source_file_name=source_file_name,
        )
        session.commit()
    except HTTPException:
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
