"""Client CLI for talking to a running ``rocq-session-server``.

Subcommands:

- ``rocq-session feedback LINE:CHAR`` — GET ``/feedback``.
- ``rocq-session health`` — GET ``/health``.
- ``rocq-session reload`` — POST ``/reload`` (reload the file from disk).
- ``rocq-session quit`` — POST ``/quit`` (asks the server to shut down).

Positions are LSP-style: 0-based line, 0-based UTF-16 character offset on that
line (matches the HTTP API the server exposes).
"""

from __future__ import annotations

import argparse
import json
import sys
from typing import Any

import httpx

DEFAULT_ENDPOINT = "http://127.0.0.1:8765"


def _parse_position(value: str) -> tuple[int, int]:
    """Parse ``LINE:CHAR`` as two non-negative ints."""
    if ":" not in value:
        raise argparse.ArgumentTypeError(
            f"expected LINE:CHAR, got {value!r}",
        )
    line_str, char_str = value.split(":", 1)
    try:
        line = int(line_str)
        character = int(char_str)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(
            f"LINE and CHAR must be integers in {value!r}",
        ) from exc
    if line < 0 or character < 0:
        raise argparse.ArgumentTypeError(
            f"LINE and CHAR must be non-negative in {value!r}",
        )
    return line, character


def _print_json(payload: Any) -> None:
    json.dump(payload, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")


def _cmd_feedback(endpoint: str, line: int, character: int) -> int:
    url = f"{endpoint.rstrip('/')}/feedback"
    try:
        response = httpx.get(url, params={"line": line, "character": character})
    except httpx.HTTPError as exc:
        print(f"request failed: {exc}", file=sys.stderr)
        return 2
    try:
        payload = response.json()
    except ValueError:
        print(
            f"non-JSON response ({response.status_code}): {response.text}",
            file=sys.stderr,
        )
        return 2
    _print_json(payload)
    return 0 if response.status_code == 200 else 1


def _cmd_health(endpoint: str) -> int:
    url = f"{endpoint.rstrip('/')}/health"
    try:
        response = httpx.get(url)
    except httpx.HTTPError as exc:
        print(f"request failed: {exc}", file=sys.stderr)
        return 2
    try:
        payload = response.json()
    except ValueError:
        print(
            f"non-JSON response ({response.status_code}): {response.text}",
            file=sys.stderr,
        )
        return 2
    _print_json(payload)
    return 0 if response.status_code == 200 else 1


_POST_OK_STATUSES = frozenset({200, 202, 204})


def _cmd_post(endpoint: str, path: str) -> int:
    url = f"{endpoint.rstrip('/')}{path}"
    try:
        response = httpx.post(url)
    except httpx.HTTPError as exc:
        print(f"request failed: {exc}", file=sys.stderr)
        return 2
    if response.status_code in _POST_OK_STATUSES:
        try:
            _print_json(response.json())
        except ValueError:
            if response.text:
                sys.stdout.write(response.text + "\n")
        return 0
    try:
        _print_json(response.json())
    except ValueError:
        print(
            f"non-JSON response ({response.status_code}): {response.text}",
            file=sys.stderr,
        )
    return 1


def _cmd_quit(endpoint: str) -> int:
    return _cmd_post(endpoint, "/quit")


def _cmd_reload(endpoint: str) -> int:
    return _cmd_post(endpoint, "/reload")


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="rocq-session",
        description="Client for rocq-session-server.",
    )
    parser.add_argument(
        "--endpoint",
        default=DEFAULT_ENDPOINT,
        help=f"Server base URL (default: {DEFAULT_ENDPOINT})",
    )

    sub = parser.add_subparsers(dest="subcommand", required=True)

    p_feedback = sub.add_parser(
        "feedback",
        help="Fetch feedback at an LSP-style position (0-based line, UTF-16 char).",
    )
    p_feedback.add_argument(
        "position",
        type=_parse_position,
        metavar="LINE:CHAR",
        help="Position as LINE:CHAR (both 0-based, LSP semantics).",
    )

    sub.add_parser("health", help="Ping the server's /health endpoint.")
    sub.add_parser("reload", help="Reload the file from disk (POST /reload).")
    sub.add_parser("quit", help="Ask the server to shut down (POST /quit).")

    return parser


def main() -> None:
    args = _build_parser().parse_args()
    if args.subcommand == "feedback":
        line, character = args.position
        sys.exit(_cmd_feedback(args.endpoint, line, character))
    if args.subcommand == "health":
        sys.exit(_cmd_health(args.endpoint))
    if args.subcommand == "reload":
        sys.exit(_cmd_reload(args.endpoint))
    if args.subcommand == "quit":
        sys.exit(_cmd_quit(args.endpoint))
    raise AssertionError(f"unknown subcommand: {args.subcommand!r}")
