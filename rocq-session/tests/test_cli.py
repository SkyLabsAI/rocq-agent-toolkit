"""Tests for the client CLI in ``rocq_session.cli``."""

from __future__ import annotations

import argparse
import asyncio
import json
from collections.abc import Iterator, Mapping
from pathlib import Path
from typing import cast
from unittest.mock import patch

import httpx
import pytest
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_session import cli
from rocq_session.testing import create_test_app


class _StubCursorEmpty:
    async def go_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        return None

    async def has_suffix(self) -> bool:
        return False

    async def run_step(
        self,
    ) -> rdm_api.CommandData | None | rdm_api.Err[rdm_api.CommandError]:
        raise AssertionError("run_step should not be called")

    async def doc_prefix(self) -> list[rdm_api.PrefixItem]:
        return []


def test_parse_position_valid() -> None:
    assert cli._parse_position("0:0") == (0, 0)
    assert cli._parse_position("3:17") == (3, 17)


def test_parse_position_invalid() -> None:
    with pytest.raises(argparse.ArgumentTypeError):
        cli._parse_position("noop")
    with pytest.raises(argparse.ArgumentTypeError):
        cli._parse_position("1:-1")
    with pytest.raises(argparse.ArgumentTypeError):
        cli._parse_position("a:b")


@pytest.fixture
def _shutdown_counter() -> list[int]:
    return []


@pytest.fixture
def _patch_httpx_to_asgi(
    tmp_path: Path, _shutdown_counter: list[int]
) -> Iterator[None]:
    """Route ``httpx.get`` / ``httpx.post`` through an ASGI transport."""
    path = tmp_path / "t.v"
    path.write_text("x", encoding="utf-8")

    def on_shutdown() -> None:
        _shutdown_counter.append(1)

    app = create_test_app(
        path, cast(RocqCursor, _StubCursorEmpty()), request_shutdown=on_shutdown
    )
    transport = httpx.ASGITransport(app=app)

    def _path_from(url: str) -> str:
        return "/" + url.split("://", 1)[-1].split("/", 1)[-1]

    def fake_get(
        url: str,
        *,
        params: Mapping[str, int] | None = None,
    ) -> httpx.Response:
        async def _do() -> httpx.Response:
            async with httpx.AsyncClient(
                transport=transport, base_url="http://test"
            ) as client:
                return await client.get(_path_from(url), params=params)

        return asyncio.run(_do())

    def fake_post(url: str) -> httpx.Response:
        async def _do() -> httpx.Response:
            async with httpx.AsyncClient(
                transport=transport, base_url="http://test"
            ) as client:
                return await client.post(_path_from(url))

        return asyncio.run(_do())

    with (
        patch.object(cli.httpx, "get", side_effect=fake_get),
        patch.object(cli.httpx, "post", side_effect=fake_post),
    ):
        yield


def test_cmd_feedback_ok(
    capsys: pytest.CaptureFixture[str], _patch_httpx_to_asgi: None
) -> None:
    rc = cli._cmd_feedback("http://ignored", 0, 0)
    assert rc == 0
    out = capsys.readouterr().out
    payload = json.loads(out)
    assert payload["status"] == "ok"


def test_cmd_feedback_bad_position(
    capsys: pytest.CaptureFixture[str], _patch_httpx_to_asgi: None
) -> None:
    rc = cli._cmd_feedback("http://ignored", 50, 0)
    assert rc == 1  # HTTP 400 → non-zero exit
    payload = json.loads(capsys.readouterr().out)
    assert "detail" in payload


def test_cmd_health_ok(
    capsys: pytest.CaptureFixture[str], _patch_httpx_to_asgi: None
) -> None:
    rc = cli._cmd_health("http://ignored")
    assert rc == 0
    assert json.loads(capsys.readouterr().out) == {"status": "ok"}


def test_cmd_quit_ok(
    capsys: pytest.CaptureFixture[str],
    _patch_httpx_to_asgi: None,
    _shutdown_counter: list[int],
) -> None:
    rc = cli._cmd_quit("http://ignored")
    assert rc == 0
    assert json.loads(capsys.readouterr().out) == {"status": "shutting_down"}
    assert _shutdown_counter == [1]
