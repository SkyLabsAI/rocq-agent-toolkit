"""
Provenance ingestion and lookup utilities.

Handles extraction of AgentClassProvenance and AgentProvenance from observability logs
and storage in the database with collision detection.
"""

import logging
from datetime import UTC, datetime
from typing import Any

from sqlmodel import Session, select

from backend.db_models import AgentClassProvenance, AgentProvenance
from backend.utils import fetch_observability_logs

logger = logging.getLogger(__name__)


# Removed extract_provenance_from_logs - use extract_provenance_from_logs_async instead
# This function was returning empty dicts and is not used anywhere in the codebase


async def extract_provenance_from_logs_async(
    run_id: str,
    task_name: str,
    estimated_time: datetime | None = None,
) -> tuple[dict[str, dict[str, Any]], dict[str, dict[str, Any]]]:
    """
    Extract AgentClassProvenance and AgentProvenance from observability logs (async).

    Args:
        run_id: The run ID to filter logs by
        task_name: The logical task name/identifier to filter logs by
        estimated_time: Optional timestamp (UTC) used to narrow the Loki query window.
            This is important during ingestion because the run/task rows may not be in
            the database yet, so we cannot estimate time from DB state.

    Returns:
        Tuple of (class_provenance_dict, instance_provenance_dict)
        where each dict maps checksum -> {cls_name/cls_provenance or name/provenance}
    """

    class_provenance: dict[str, dict[str, Any]] = {}
    instance_provenance: dict[str, dict[str, Any]] = {}

    try:
        # Ensure UTC-awareness
        if estimated_time is not None and estimated_time.tzinfo is None:
            estimated_time = estimated_time.replace(tzinfo=UTC)

        # Fetch observability logs
        logs = await fetch_observability_logs(
            run_id=run_id, task_name=task_name, estimated_time=estimated_time
        )

        # Extract provenance entries from logs
        # The logs are structured as JSON, so we need to parse the log line
        import json

        for log in logs:
            if not log.line:
                continue

            try:
                # Try to parse the log line as JSON
                # The log line from Loki should contain JSON with the log data
                log_data = json.loads(log.line)

                # Check for AgentClassProvenance
                # The message field should contain "AgentClassProvenance"
                message = log_data.get("message", "")
                if message == "AgentClassProvenance":
                    cls_checksum = log_data.get("cls_checksum")
                    if cls_checksum:
                        cls_name = log_data.get("cls_name", "")
                        cls_provenance_json = log_data.get(
                            "cls_provenance.cls_provenance", "{}"
                        )

                        # Parse JSON if it's a string
                        if isinstance(cls_provenance_json, str):
                            try:
                                cls_provenance_data = json.loads(cls_provenance_json)
                            except (json.JSONDecodeError, TypeError):
                                cls_provenance_data = {}
                        else:
                            cls_provenance_data = cls_provenance_json

                        class_provenance[cls_checksum] = {
                            "cls_name": cls_name,
                            "cls_provenance": cls_provenance_data,
                        }

                # Check for AgentProvenance
                if message == "AgentProvenance":
                    checksum = log_data.get("checksum")
                    if checksum:
                        name = log_data.get("name", "")
                        cls_checksum = log_data.get(
                            "cls_checksum", ""
                        )  # For correlation
                        provenance_json = log_data.get("provenance.provenance", "{}")

                        # Parse JSON if it's a string
                        if isinstance(provenance_json, str):
                            try:
                                provenance_data = json.loads(provenance_json)
                            except (json.JSONDecodeError, TypeError):
                                provenance_data = {}
                        else:
                            provenance_data = provenance_json

                        instance_provenance[checksum] = {
                            "name": name,
                            "cls_checksum": cls_checksum,
                            "provenance": provenance_data,
                        }
            except (json.JSONDecodeError, KeyError, TypeError):
                # Skip logs that don't match the expected format
                continue

    except Exception as e:  # pylint: disable=broad-exception-caught
        logger.warning(
            "Error extracting provenance from logs for run_id=%s, task_name=%s: %s",
            run_id,
            task_name,
            e,
        )

    return class_provenance, instance_provenance


def ingest_agent_class_provenance(
    session: Session,
    cls_checksum: str,
    cls_name: str,
    cls_provenance: dict[str, Any],
) -> AgentClassProvenance:
    """
    Ingest agent class provenance into the database with collision detection.

    Args:
        session: Database session
        cls_checksum: The class checksum (primary key)
        cls_name: The class name
        cls_provenance: The class provenance data

    Returns:
        The AgentClassProvenance record

    Raises:
        ValueError: If collision detected (same checksum, different name/provenance)
    """
    # Check if record exists
    stmt = select(AgentClassProvenance).where(
        AgentClassProvenance.cls_checksum == cls_checksum
    )
    existing = session.exec(stmt).first()

    if existing is not None:
        # Collision detection
        if existing.cls_name != cls_name:
            error_msg = (
                f"Collision detected for cls_checksum={cls_checksum}: "
                f"existing cls_name='{existing.cls_name}' != new cls_name='{cls_name}'"
            )
            logger.error(error_msg)
            raise ValueError(error_msg)

        # Check if provenance differs (compare as JSON strings for simplicity)
        import json

        existing_prov_json = json.dumps(existing.cls_provenance, sort_keys=True)
        new_prov_json = json.dumps(cls_provenance, sort_keys=True)
        if existing_prov_json != new_prov_json:
            error_msg = (
                f"Collision detected for cls_checksum={cls_checksum}: "
                f"provenance data differs"
            )
            logger.error(error_msg)
            raise ValueError(error_msg)

        # No collision, return existing
        return existing

    # Create new record
    new_record = AgentClassProvenance(
        cls_checksum=cls_checksum,
        cls_name=cls_name,
        cls_provenance=cls_provenance,
    )
    session.add(new_record)
    session.flush()
    return new_record


def ingest_agent_provenance(
    session: Session,
    agent_checksum: str,
    cls_checksum: str,
    name: str,
    provenance: dict[str, Any],
) -> AgentProvenance:
    """
    Ingest agent instance provenance into the database with collision detection.

    Args:
        session: Database session
        agent_checksum: The agent checksum (primary key)
        name: The agent instance name
        provenance: The agent provenance data

    Returns:
        The AgentProvenance record

    Raises:
        ValueError: If collision detected (same checksum, different name/provenance)
    """
    # Check if record exists
    stmt = select(AgentProvenance).where(
        AgentProvenance.agent_checksum == agent_checksum
    )
    existing = session.exec(stmt).first()

    if existing is not None:
        # Collision detection
        if existing.name != name:
            error_msg = (
                f"Collision detected for agent_checksum={agent_checksum}: "
                f"existing name='{existing.name}' != new name='{name}'"
            )
            logger.error(error_msg)
            raise ValueError(error_msg)

        if existing.cls_checksum != cls_checksum:
            error_msg = (
                f"Collision detected for agent_checksum={agent_checksum}: "
                f"existing cls_checksum='{existing.cls_checksum}' != new cls_checksum='{cls_checksum}'"
            )
            logger.error(error_msg)
            raise ValueError(error_msg)

        # Check if provenance differs
        import json

        existing_prov_json = json.dumps(existing.provenance, sort_keys=True)
        new_prov_json = json.dumps(provenance, sort_keys=True)
        if existing_prov_json != new_prov_json:
            error_msg = (
                f"Collision detected for agent_checksum={agent_checksum}: "
                f"provenance data differs"
            )
            logger.error(error_msg)
            raise ValueError(error_msg)

        # No collision, return existing
        return existing

    # Create new record
    new_record = AgentProvenance(
        agent_checksum=agent_checksum,
        cls_checksum=cls_checksum,
        name=name,
        provenance=provenance,
    )
    session.add(new_record)
    session.flush()
    return new_record
