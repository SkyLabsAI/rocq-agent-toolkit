"""CLI entry point for the ``rocq-session-server`` HTTP server."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

import uvicorn

from .main import create_app


def _split_argv_at_double_dash(argv: list[str]) -> tuple[list[str], list[str]]:
    if "--" in argv:
        idx = argv.index("--")
        return argv[:idx], argv[idx + 1 :]
    return argv, []


def _run_server(
    file_path: Path,
    rocq_args: list[str],
    *,
    host: str,
    port: int,
    cwd: Path | None,
    log_level: str = "info",
) -> None:
    """Build the app, wire ``POST /quit`` to the uvicorn server, and serve."""
    app = create_app(file_path, rocq_args, cwd=cwd)
    config = uvicorn.Config(app=app, host=host, port=port, log_level=log_level)
    server = uvicorn.Server(config)

    def _request_shutdown() -> None:
        server.should_exit = True

    app.state.request_shutdown = _request_shutdown
    server.run()


def main() -> None:
    front, rocq_args = _split_argv_at_double_dash(sys.argv[1:])
    parser = argparse.ArgumentParser(
        prog="rocq-session-server",
        description="HTTP server for one Rocq file (rocq-doc-manager).",
    )
    parser.add_argument(
        "file",
        type=Path,
        help="Path to the .v file to load",
    )
    parser.add_argument(
        "--host",
        default="127.0.0.1",
        help="Bind address (default: 127.0.0.1)",
    )
    parser.add_argument(
        "--port",
        type=int,
        default=8765,
        help="TCP port (default: 8765)",
    )
    parser.add_argument(
        "--cwd",
        type=Path,
        default=None,
        help="Working directory for the document manager subprocess",
    )
    args = parser.parse_args(front)

    path = args.file
    if not str(path).endswith(".v"):
        parser.error("FILE must be a .v file")

    cwd = args.cwd.resolve() if args.cwd is not None else None
    _run_server(
        path.resolve(),
        rocq_args,
        host=args.host,
        port=args.port,
        cwd=cwd,
    )
