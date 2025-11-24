"""
FastAPI backend server for Rocq_agent task results.
Phase 1: Local file-based data access with in-memory storage.
"""
from typing import List
import logging

from fastapi import FastAPI, HTTPException, Query
from fastapi.middleware.cors import CORSMiddleware
from contextlib import asynccontextmanager

from backend.config import settings
from backend.data_access import data_store
from backend.models import (
    AgentInfo,
    RunInfo,
    RunDetailsResponse,
    ObservabilityLogsResponse,
    RefreshResponse,
    ObservabilityLabelsResponse,
    TagsResponse,
)
from backend.utils import get_labels_grouped_by_log, fetch_observability_logs
import uvicorn

# Configure logging
logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s"
)
logger = logging.getLogger(__name__)


@asynccontextmanager
async def lifespan(app: FastAPI):
    """
    Lifespan context manager for startup and shutdown events.
    Loads JSONL data on startup.
    """
    logger.info("Starting FastAPI backend...")
    logger.info(f"Loading JSONL files from: {settings.jsonl_results_path}")

    try:
        results_path = settings.get_results_path()
        count = data_store.load_from_directory(results_path)
        logger.info(f"Successfully loaded {count} task results")

    except FileNotFoundError as e:
        logger.error(f"Directory not found: {e}")
        logger.warning("Server will start but no data is available")
    except Exception as e:
        logger.error(f"Error loading data: {e}")
        logger.warning("Server will start but no data is available")

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
async def root():
    """Root endpoint - health check."""
    return {
        "message": "Rocq Agent Toolkit Backend API",
        "version": "1.0.0",
        "status": "running",
    }


@app.get("/api/agents", response_model=List[AgentInfo])
async def list_agents():
    """
    List all unique agents found in the JSONL files.

    Returns:
        List of AgentInfo objects containing agent names and run counts
    """
    try:
        agents = data_store.get_all_agents()
        return agents
    except Exception as e:
        logger.error(f"Error fetching agents: {e}")
        raise HTTPException(status_code=500, detail=f"Error fetching agents: {str(e)}")


@app.get("/api/agents/{agent_name}/runs", response_model=List[RunInfo])
async def list_runs_by_agent(agent_name: str):
    """
    List all runs for a specific agent.

    Args:
        agent_name: Name of the agent

    Returns:
        List of RunInfo objects for the specified agent
    """
    try:
        runs = data_store.get_runs_by_agent(agent_name)

        if not runs:
            # Check if agent exists
            agents = data_store.get_all_agents()
            agent_names = [agent.agent_name for agent in agents]

            if agent_name not in agent_names:
                raise HTTPException(
                    status_code=404, detail=f"Agent '{agent_name}' not found"
                )

        return runs
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Error fetching runs for agent '{agent_name}': {e}")
        raise HTTPException(status_code=500, detail=f"Error fetching runs: {str(e)}")


@app.get("/api/runs/details", response_model=List[RunDetailsResponse])
async def get_run_details(
    run_ids: str = Query(..., description="Comma-separated list of run IDs to retrieve")
):
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
        results = data_store.get_run_details(id_list)

        if not results:
            raise HTTPException(
                status_code=404, detail=f"No runs found for the provided run_ids"
            )

        return results
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Error fetching run details: {e}")
        raise HTTPException(
            status_code=500, detail=f"Error fetching run details: {str(e)}"
        )


@app.get("/api/health")
async def health_check():
    """
    Health check endpoint.

    Returns:
        System status information
    """
    agents = data_store.get_all_agents()
    total_tasks = len(data_store.task_results)

    return {
        "status": "healthy",
        "total_agents": len(agents),
        "total_tasks": total_tasks,
        "config": {
            "jsonl_results_path": settings.jsonl_results_path,
            "observability_url": settings.observability_url,
        },
    }


@app.get("/api/tags", response_model=TagsResponse)
async def list_tags() -> TagsResponse:
    """
    List all unique metadata tags across all tasks.

    Returns:
        TagsResponse containing tag keys and their unique values.
    """
    try:
        # Pylint may not see dynamically added methods on the DataStore singleton.
        tags_response = data_store.get_unique_tags()  # pylint: disable=no-member
        return tags_response
    except Exception as e:
        logger.error(f"Error fetching tags: {e}", exc_info=True)
        raise HTTPException(
            status_code=500, detail=f"Error fetching tags: {str(e)}"
        ) from e


# Change it to the POST
@app.post("/api/refresh", response_model=RefreshResponse)
async def refresh_data():
    """
    Refresh data by reloading all JSONL files from the configured directory.

    This endpoint clears all existing data and reloads from disk, allowing
    the server to pick up new files without restarting.

    Returns:
        RefreshResponse with status and statistics
    """
    try:
        logger.info("Refreshing data from JSONL files...")
        results_path = settings.get_results_path()
        count = data_store.reload_from_directory(results_path)

        agents = data_store.get_all_agents()

        logger.info(f"Refresh complete: {count} task results loaded")

        return RefreshResponse(
            success=True,
            message=f"Successfully reloaded {count} task results from {len(agents)} agents",
            total_tasks=count,
            total_agents=len(agents),
        )
    except FileNotFoundError as e:
        logger.error(f"Directory not found during refresh: {e}")
        raise HTTPException(
            status_code=404,
            detail=f"JSONL directory not found: {settings.jsonl_results_path}",
        )
    except Exception as e:
        logger.error(f"Error refreshing data: {e}")
        raise HTTPException(status_code=500, detail=f"Error refreshing data: {str(e)}")


@app.get("/api/observability/logs/raw", response_model=ObservabilityLogsResponse)
async def get_observability_logs_raw(
    run_id: str = Query(..., description="Run ID to fetch logs for"),
    task_id: str = Query(..., description="Task ID to fetch logs for"),
):
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
        ObservabilityLabelsResponse containing unique label key-value pairs

    Example:
        /api/observability/logs/raw?run_id=abc123&task_id=task456
    """
    try:
        logs = await fetch_observability_logs(run_id=run_id, task_id=task_id)

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
        )
        




@app.get("/api/observability/logs", response_model=ObservabilityLabelsResponse)
async def get_observability_logs(
    run_id: str = Query(..., description="Run ID to fetch logs for"),
    task_id: str = Query(..., description="Task ID to fetch logs for"),
):
    """
    Fetch observability log labels from Loki for a specific run and task.

    This endpoint uses the shared utility function in `utils.py` to fetch
    raw logs from Loki, then performs postprocessing to aggregate labels.

    Returns only the unique labels from the logs after filtering.

    Example:
        /api/observability/logs?run_id=abc123&task_id=task456
    """
    try:
        # Fetch raw logs via shared utility
        logs = await fetch_observability_logs(run_id=run_id, task_id=task_id)

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
        )


if __name__ == "__main__":

    uvicorn.run(
        "main:app",
        host=settings.server_host,
        port=settings.server_port,
        reload=True,
        log_level=settings.log_level,
    )
