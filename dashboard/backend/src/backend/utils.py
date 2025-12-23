"""
Utility functions for the backend.
"""

import logging
from datetime import UTC, datetime, timedelta
from typing import Any

import httpx
from fastapi import HTTPException

from backend.config import settings
from backend.models import LogEntry

logger = logging.getLogger(__name__)


# Labels to exclude from log entries
EXCLUDED_LABELS = {
    "code_file_path",
    "code_function_name",
    "code_line_number",
    "detected_level",
    "file",
    "function",
    "key_caller_info_file",
    "key_caller_info_function",
    "key_caller_info_line",
    "level",
    "line",
    "logger",
    "observed_timestamp",
    "run_id",
    "scope_name",
    "service",
    "service_name",
    "service_namespace",
    "service_version",
    "severity_number",
    "severity_text",
    "task_id",
    "telemetry_sdk_language",
    "telemetry_sdk_name",
    "telemetry_sdk_version",
    "timestamp",
    "message",
}


def filter_log_labels(labels: dict[str, Any]) -> dict[str, Any]:
    """
    Filter out unwanted labels from log entries.

    Args:
        labels: Dictionary of labels from Loki

    Returns:
        Filtered dictionary with excluded labels removed
    """
    return {key: value for key, value in labels.items() if key not in EXCLUDED_LABELS}


def get_labels_grouped_by_log(
    logs: list[LogEntry],
    marker: str = "status",
    group_name: str = "groups",
) -> dict[str, list[dict[str, Any]]]:
    """
    Group related log labels into items delimited by a marker label.

    This is meant for observability-style UIs where a sequence of logs
    (e.g. tactic prediction, explanations, etc.) should be grouped
    together once a terminal label such as ``status`` appears.

    The algorithm assumes:
    - logs are in chronological order (as returned by Loki),
    - the marker label (by default ``\"status\"``) appears once per group,
      typically on the last log of that group.

    Args:
        logs: List of LogEntry objects containing filtered labels.
        marker: Label key that closes the current group when present.

    Returns:
        A dictionary with a single key ``\"groups\"`` whose value is a list
        of dictionaries. Each dictionary represents one grouped item and
        contains the merged labels from all logs in that group.
    """
    groups: list[dict[str, Any]] = []
    current_group: dict[str, Any] = {}

    for log in logs:
        if not log.labels:
            continue

        # Merge all labels from this log into the current group.
        # If a key appears multiple times within a group, the latest
        # value wins, which matches the intuition of "most recent state".
        for key, value in log.labels.items():
            current_group[key] = str(value)

        # When we see the marker, we consider the current group complete.
        if marker in log.labels:
            if current_group:
                groups.append(current_group)
            current_group = {}

    # If there is a trailing, incomplete group without a marker,
    # we still return it so the UI can decide how to render it.
    if current_group:
        groups.append(current_group)

    return {group_name: groups}


async def fetch_observability_logs(
    run_id: str,
    task_id: str,
    estimated_time: datetime | None = None,
) -> list[LogEntry]:
    """
    Fetch observability logs from Loki for a specific run and task.

    This function is responsible only for querying Loki and returning
    a sorted list of LogEntry objects. Any further post-processing of
    the logs (e.g., aggregating labels) should be done by the caller.

    Args:
        run_id: The run ID to filter logs by.
        task_id: The task ID to filter logs by.

    Returns:
        List of LogEntry items sorted by timestamp.

    Raises:
        HTTPException: If there is an error communicating with Loki
                       or if Loki is unavailable.
    """
    try:
        # Construct LogQL query to filter logs
        # run_id and task_id are JSON fields, not labels, so we need to parse JSON and filter
        logql_query = f'{{service_name="rocq_agent"}} | json | run_id="{run_id}" | task_id="{task_id}"'

        # Calculate time range based on the task's estimated time (if provided).
        # We take a symmetric window of ±delta_hours around the task timestamp.
        delta = timedelta(hours=settings.log_query_time_delta_hours)

        if estimated_time is not None:
            start_time = estimated_time - delta
            end_time = estimated_time + delta
        else:
            # Fallback to a window around "now" if we cannot estimate
            end_time = datetime.now(UTC)
            start_time = end_time - timedelta(days=settings.log_query_time_delta_days)

        # Query parameters for Loki
        params: dict[str, str | int | bool | float] = {
            "query": logql_query,
            "start": start_time.strftime("%Y-%m-%dT%H:%M:%SZ"),
            "end": end_time.strftime("%Y-%m-%dT%H:%M:%SZ"),
            "direction": "backward",
            "limit": 5000,  # Maximum number of logs to return
        }

        logger.info("Querying Loki for logs: run_id=%s, task_id=%s", run_id, task_id)
        logger.info("LogQL query: %s", logql_query)

        # Make request to Loki
        loki_url = f"{settings.observability_url}/loki/api/v1/query_range"

        async with httpx.AsyncClient(timeout=30.0) as client:
            response = await client.get(loki_url, params=params)

            if response.status_code == 404:
                # Loki not available
                raise HTTPException(
                    status_code=503,
                    detail=f"Loki service not available at {settings.observability_url}",
                )

            response.raise_for_status()
            data = response.json()

        # Parse Loki response
        logs: list[LogEntry] = []

        if data.get("status") == "success":
            result = data.get("data", {}).get("result", [])

            for stream in result:
                stream_labels = stream.get("stream", {})
                values = stream.get("values", [])

                for value in values:
                    # Loki returns [timestamp_ns, log_line]
                    timestamp_ns = value[0]
                    log_line = value[1]

                    # Convert nanosecond timestamp to ISO format
                    timestamp_sec = int(timestamp_ns) / 1_000_000_000
                    timestamp_iso = datetime.fromtimestamp(timestamp_sec).isoformat()

                    # Filter out unwanted labels before sending to frontend
                    filtered_labels = filter_log_labels(stream_labels)

                    logs.append(
                        LogEntry(
                            timestamp=timestamp_iso,
                            line=log_line,
                            labels=filtered_labels,
                        )
                    )

        # Sort logs by timestamp
        logs.sort(key=lambda x: x.timestamp)

        logger.info("Retrieved %d log entries from Loki", len(logs))

        return logs

    except httpx.HTTPStatusError as e:
        logger.error("Loki HTTP error: %s", e)
        raise HTTPException(
            status_code=502,
            detail=f"Error communicating with Loki: {e.response.status_code}",
        ) from e
    except httpx.RequestError as e:
        logger.error("Loki request error: %s", e)
        raise HTTPException(
            status_code=503,
            detail=f"Could not connect to Loki at {settings.observability_url}",
        ) from e
    except HTTPException:
        # Re-raise HTTPException as-is to preserve status and detail
        raise
    except Exception as e:
        logger.error("Error fetching observability logs: %s", e, exc_info=True)
        raise HTTPException(
            status_code=500, detail=f"Error fetching logs: {str(e)}"
        ) from e
