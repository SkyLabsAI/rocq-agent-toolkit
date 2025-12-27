"""
Batch ingest all files from a directory into the Rocq Agent Toolkit backend.

Usage:
    uv run python -m client.batch_ingester /path/to/results_folder \
        --base-url http://localhost:8000
"""

import argparse
import sys
from pathlib import Path

from client.ingester import DEFAULT_BASE_URL, ingest_file


def batch_ingest(
    directory: str | Path,
    base_url: str = DEFAULT_BASE_URL,
    timeout: float = 60.0,
) -> None:
    dir_path = Path(directory)
    if not dir_path.is_dir():
        print(f"Error: {dir_path} is not a directory.")
        sys.exit(1)

    # Iterate over all files in the directory
    # Sort them to have a deterministic order
    files = sorted([f for f in dir_path.iterdir() if f.is_file()])

    if not files:
        print(f"No files found in {dir_path}")
        return

    print(f"Found {len(files)} files in {dir_path}. Starting ingestion...")
    print("-" * 50)

    success_count = 0
    fail_count = 0

    for file_path in files:
        print(f"Ingesting {file_path.name}...", end=" ", flush=True)
        try:
            result = ingest_file(
                file_path=file_path, base_url=base_url, timeout=timeout
            )

            # Check logical success from the API response if available
            if result.get("success"):
                print("SUCCESS")
                success_count += 1
            else:
                msg = result.get("message", "Unknown error")
                print(f"FAILED (API error: {msg})")
                fail_count += 1

        except Exception as e:
            print(f"FAILED (Exception: {e})")
            fail_count += 1

    print("-" * 50)
    print("Batch ingestion complete.")
    print(f"Successful: {success_count}")
    print(f"Failed:     {fail_count}")


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Batch ingest files from a folder into the Rocq Agent Toolkit backend."
    )
    parser.add_argument(
        "directory",
        type=str,
        help="Directory containing files to ingest.",
    )
    parser.add_argument(
        "--base-url",
        type=str,
        default=DEFAULT_BASE_URL,
        help="Base URL of the backend (default: %(default)s).",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=60.0,
        help="Request timeout in seconds per file (default: %(default)s).",
    )
    return parser.parse_args()


def main() -> None:
    args = _parse_args()
    batch_ingest(
        directory=args.directory,
        base_url=args.base_url,
        timeout=args.timeout,
    )


if __name__ == "__main__":
    main()
