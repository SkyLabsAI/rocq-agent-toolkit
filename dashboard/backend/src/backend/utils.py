"""
Utility functions for the backend.
"""
from typing import Dict, Any, List
from backend.models import LogEntry


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


def get_labels(logs: List[LogEntry]) -> Dict[str, List[str]]:
    """
    Extract labels from a list of log entries.

    Args:
        logs: List of LogEntry objects containing filtered labels

    Returns:
        Dictionary where each key maps to a list of all values found across all logs
    """
    labels_dict: Dict[str, List[str]] = {}

    for log in logs:
        if log.labels:
            for key, value in log.labels.items():
                # Add all values, including duplicates
                if key not in labels_dict:
                    labels_dict[key] = []
                labels_dict[key].append(str(value))

    return labels_dict
