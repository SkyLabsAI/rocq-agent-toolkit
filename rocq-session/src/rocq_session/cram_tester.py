"""Cram testing program for rocq-session operations without server startup."""

from __future__ import annotations

import asyncio
import json
import logging
import sys
from pathlib import Path
from typing import Any

from rocq_doc_manager import create
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

from .feedback import FeedbackCache
from .session_ops import (
    CursorPayload,
    InsertPayload,
    QueryPayload,
    cursor_location,
    insert_command,
    run_query,
)

logger = logging.getLogger(__name__)


def parse_command_call(s: str) -> tuple[str, dict[str, Any]]:
    """Parse a JSON command call string into command name and arguments."""
    try:
        js = json.loads(s)
        if isinstance(js, str):
            # Just a command name with no arguments
            return (js, {})
        if isinstance(js, list) and len(js) == 2:
            # [command_name, args_dict]
            return (js[0], js[1])
        raise ValueError(f"Invalid command format: {s}")
    except json.JSONDecodeError:
        # If it's not valid JSON, treat it as a bare command name
        return (s, {})


async def execute_session_command(
    cursor: Any,
    cache: FeedbackCache,
    lock: asyncio.Lock,
    command: str,
    args: dict[str, Any],
) -> None:
    """Execute a session command and print the result."""
    try:
        if command == "cursor":
            cursor_result: CursorPayload = await cursor_location(cursor, lock)
            print(f"= {json.dumps(cursor_result)}")

        elif command == "query":
            text = args["text"]
            line = args.get("line")
            character = args.get("character")

            query_result: QueryPayload = await run_query(
                cursor,
                cache,
                lock,
                text=text,
                line=line,
                character=character,
            )
            print(f"= {json.dumps(query_result)}")

        elif command == "insert":
            text = args["text"]
            line = args.get("line")
            character = args.get("character")

            insert_result: InsertPayload = await insert_command(
                cursor,
                cache,
                lock,
                text=text,
                line=line,
                character=character,
            )
            print(f"= {json.dumps(insert_result)}")

        else:
            print(f"= {json.dumps({'error': f'Unknown command: {command}'})}")

    except Exception as exc:
        print(f"= {json.dumps({'error': str(exc)})}")


async def run_session_test(
    file_path: Path,
    commands: list[tuple[str, dict[str, Any]]],
    rocq_args: list[str] | None = None,
) -> None:
    """Run session commands against a Rocq document."""
    if not file_path.exists():
        print(f"Error: File {file_path} does not exist")
        sys.exit(1)

    # Initialize RocqDocManager
    try:
        rdm = await create(str(file_path), rocq_args=rocq_args or [])
        load_reply = await rdm.load_file(0)
        if isinstance(load_reply, rdm_api.Err):
            msg = f"RocqDocManager.load_file failed: {load_reply.message}"
            raise RuntimeError(msg)

        cursor = rdm.cursor()
        lock = asyncio.Lock()
        cache = FeedbackCache()

        try:
            # Execute each command
            for command, args in commands:
                print(f"{command}({json.dumps(args)})")
                await execute_session_command(cursor, cache, lock, command, args)

        finally:
            # Clean up
            try:
                await rdm.quit()
            except rdm_api.Error as exc:
                logger.info("RDM already stopped at shutdown: %s", exc)
            except Exception as exc:
                logger.warning("RDM shutdown error: %s", exc)

    except Exception as exc:
        print(f"Fatal error: {exc}")
        sys.exit(1)


async def amain(args: list[str]) -> None:
    """Main async function following the tool-tester pattern."""
    if len(args) < 1:
        raise ValueError("Need at least one argument (file path)")

    file_path = Path(args.pop(0))

    # Parse command calls from remaining arguments
    commands = [parse_command_call(arg) for arg in args]

    # Use "dune" as rocq_args if file is in a dune project
    rocq_args = ["dune"] if (file_path.parent / "dune").exists() else []

    await run_session_test(file_path, commands, rocq_args)


def main() -> None:
    """Main entry point for the cram tester."""
    if len(sys.argv) < 2:
        print("Usage: rocq-session-cram-test <file.v> [command_json_args...]")
        print()
        print("Examples:")
        print(
            '  rocq-session-cram-test test.v "cursor" \'["insert", {"text": "Definition x := 0."}]\''
        )
        print(
            '  echo \'["query", {"text": "Check nat."}]\' | rocq-session-cram-test test.v "cursor"'
        )
        sys.exit(1)

    # Set up logging
    logging.basicConfig(
        level=logging.WARNING,
        format="%(name)s:%(levelname)s: %(message)s",
    )

    try:
        asyncio.run(amain(sys.argv[1:]))
    except KeyboardInterrupt:
        print("\nInterrupted")
        sys.exit(1)
    except Exception as exc:
        print(f"Fatal error: {exc}")
        sys.exit(1)


if __name__ == "__main__":
    main()
