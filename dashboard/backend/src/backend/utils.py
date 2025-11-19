"""
Utility functions for the backend.
"""
from typing import Dict, Any, List, Union, Optional
from datetime import datetime, timedelta
import logging

import httpx
from fastapi import HTTPException

from backend.config import settings
from backend.models import LogEntry
from backend.data_access import data_store


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


def filter_log_labels(labels: Dict[str, Any]) -> Dict[str, Any]:
    """
    Filter out unwanted labels from log entries.

    Args:
        labels: Dictionary of labels from Loki

    Returns:
        Filtered dictionary with excluded labels removed
    """
    return {key: value for key, value in labels.items() if key not in EXCLUDED_LABELS}


def get_labels(
    logs: List[LogEntry], group_by: List[str] = None
) -> Dict[str, List[Union[str, Dict[str, Any]]]]:
    """
    Extract labels from a list of log entries.

    Args:
        logs: List of LogEntry objects containing filtered labels
        group_by: List of prefixes to group labels by

    Returns:
        Dictionary where each key maps to a list of all values found across all logs.
        If a label matches a group_by prefix, it is added to that group as a dict {key: value}.
        Otherwise, it is added as a string value.
    """
    if group_by is None:
        group_by = []

    # First, collect all values for all keys
    raw_labels: Dict[str, List[str]] = {}

    for log in logs:
        if log.labels:
            for key, value in log.labels.items():
                if key not in raw_labels:
                    raw_labels[key] = []
                raw_labels[key].append(str(value))

    final_labels: Dict[str, List[Union[str, Dict[str, Any]]]] = {}
    processed_keys = set()

    # Process groups
    for prefix in group_by:
        # Find all keys that start with this prefix
        group_keys = [k for k in raw_labels.keys() if k.startswith(prefix)]

        if not group_keys:
            continue

        # Mark these keys as processed
        processed_keys.update(group_keys)

        # Group by index
        # Find the maximum length of lists in this group
        max_len = 0
        for k in group_keys:
            max_len = max(max_len, len(raw_labels[k]))

        group_list = []
        for i in range(max_len):
            item_dict = {}
            for k in group_keys:
                if i < len(raw_labels[k]):
                    item_dict[k] = raw_labels[k][i]
            group_list.append(item_dict)

        final_labels[prefix] = group_list

    # Add remaining non-grouped labels
    for key, values in raw_labels.items():
        if key not in processed_keys:
            final_labels[key] = values

    return final_labels

# Adding this for now since LOKI requires a Time Range for the query
# So we are taking a estimated time of the start and using a delta , find a time range to query the logs.
# In Production system, we might be doing something else.
def get_estimated_time(run_id: str, task_id: str) -> Optional[datetime]:
    """
    Estimate when logs were generated for a given run and task based on
    the `timestamp_utc` field from the corresponding `TaskResult`.
    """
    task = next(
        (
            t
            for t in data_store.task_results
            if t.run_id == run_id and t.task_id == task_id
        ),
        None,
    )

    if task is None:
        logger.warning("No TaskResult found when estimating time for run_id=%s, task_id=%s", run_id, task_id)
        return None

    raw_ts = task.timestamp_utc
    if not raw_ts:
        logger.warning("Empty timestamp_utc for run_id=%s, task_id=%s", run_id, task_id)
        return None

    # Normalise to an ISO string that `datetime.fromisoformat` understands
    normalised_ts = raw_ts.replace("Z", "+00:00") if raw_ts.endswith("Z") else raw_ts

    try:
        estimated_dt = datetime.fromisoformat(normalised_ts)
    except ValueError:
        logger.warning("Failed to parse timestamp_utc='%s' for run_id=%s, task_id=%s", raw_ts, run_id, task_id)
        return None

    logger.info("Estimated log time for run_id=%s, task_id=%s: %s", run_id, task_id, estimated_dt.isoformat())
    return estimated_dt


async def fetch_observability_logs(run_id: str, task_id: str) -> List[LogEntry]:
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
        logql_query = (
            f'{{service_name="rocq_agent"}} | json | run_id="{run_id}" | task_id="{task_id}"'
        )

        # Calculate time range based on the task's estimated time.
        # We take a symmetric window of ±delta_hours around the task timestamp.
        delta = timedelta(hours=settings.log_query_time_delta_hours)

        estimated_time = get_estimated_time(run_id, task_id)
        if estimated_time is not None:
            start_time = estimated_time - delta
            end_time = estimated_time + delta
        else:
            # Fallback to a window around "now" if we cannot estimate
            end_time = datetime.utcnow()
            start_time = end_time - timedelta(days=settings.log_query_time_delta_days)

        # Query parameters for Loki
        params = {
            "query": logql_query,
            "start": start_time.strftime("%Y-%m-%dT%H:%M:%SZ"),
            "end": end_time.strftime("%Y-%m-%dT%H:%M:%SZ"),
            "direction": "backward",
            "limit": 5000,  # Maximum number of logs to return
        }

        logger.info(
            "Querying Loki for logs: run_id=%s, task_id=%s", run_id, task_id
        )
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
        logs: List[LogEntry] = []

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
        )
    except httpx.RequestError as e:
        logger.error("Loki request error: %s", e)
        raise HTTPException(
            status_code=503,
            detail=f"Could not connect to Loki at {settings.observability_url}",
        )
    except HTTPException:
        # Re-raise HTTPException as-is to preserve status and detail
        raise
    except Exception as e:
        logger.error("Error fetching observability logs: %s", e, exc_info=True)
        raise HTTPException(status_code=500, detail=f"Error fetching logs: {str(e)}")
