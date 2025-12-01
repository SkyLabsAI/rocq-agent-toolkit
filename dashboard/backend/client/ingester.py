"""
Simple client script to ingest a JSONL file into the Rocq Agent Toolkit backend.

Usage:
    python -m backend.client.ingester /path/to/results.jsonl \
        --base-url http://localhost:8004 \
        --source-file-name tasks_results.jsonl

The backend must be running and exposing the /api/ingest endpoint.
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any

import httpx


DEFAULT_BASE_URL = "http://localhost:8004"
INGEST_PATH = "/api/ingest"


def ingest_file(
    file_path: str | Path,
    base_url: str = DEFAULT_BASE_URL,
    source_file_name: str | None = None,
    timeout: float = 60.0,
) -> dict[str, Any]:
    """
    Upload a JSONL file to the backend /api/ingest endpoint using the
    `file` upload option.

    Args:
        file_path: Path to the JSONL file containing task results.
        base_url: Base URL of the backend (e.g. http://localhost:8004).
        source_file_name: Optional logical name recorded in the DB; if not
            provided, the file's name on disk is used.
        timeout: Request timeout in seconds.

    Returns:
        Parsed JSON response from the backend.
    """
    path = Path(file_path)
    if not path.is_file():
        raise FileNotFoundError(f"Input file does not exist: {path}")

    if source_file_name is None:
        source_file_name = path.name

    url = f"{base_url.rstrip('/')}{INGEST_PATH}"
    params = {"source_file_name": source_file_name}

    # FastAPI endpoint is declared with `file: UploadFile | None = File(...)`,
    # so the reliable way to use it is via multipart/form-data file upload.
    with path.open("rb") as f:
        files = {"file": (path.name, f, "application/jsonl")}
        with httpx.Client(timeout=timeout) as client:
            response = client.post(url, files=files, params=params)

    response.raise_for_status()
    return response.json()


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Ingest a JSONL file into the Rocq Agent Toolkit backend."
    )
    parser.add_argument(
        "file",
        type=str,
        help="Path to the JSONL file containing task results.",
    )
    parser.add_argument(
        "--base-url",
        type=str,
        default=DEFAULT_BASE_URL,
        help="Base URL of the backend (default: %(default)s).",
    )
    parser.add_argument(
        "--source-file-name",
        type=str,
        default=None,
        help=(
            "Optional logical name for the ingested file; "
            "defaults to the basename of the local file."
        ),
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=60.0,
        help="Request timeout in seconds (default: %(default)s).",
    )
    return parser.parse_args()


def main() -> None:
    args = _parse_args()
    result = ingest_file(
        file_path=args.file,
        base_url=args.base_url,
        source_file_name=args.source_file_name,
        timeout=args.timeout,
    )
    # Print a concise human-readable summary
    success = result.get("success")
    message = result.get("message", "")
    runs = result.get("runs_ingested")
    tasks = result.get("tasks_ingested")

    print(f"Success: {success}")
    if message:
        print(message)
    if runs is not None and tasks is not None:
        print(f"Runs ingested: {runs}, Tasks ingested: {tasks}")


if __name__ == "__main__":
    main()


