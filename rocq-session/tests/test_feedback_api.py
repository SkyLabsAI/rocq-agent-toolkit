"""HTTP tests for ``/feedback`` using ``httpx.ASGITransport``."""

from __future__ import annotations

from pathlib import Path
from typing import cast

import httpx
import pytest
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_session.testing import create_test_app


class _StubCursorEmpty:
    """Minimal cursor: empty document, nothing to step."""

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


@pytest.mark.asyncio
async def test_feedback_ok_empty_via_asgi(tmp_path: Path) -> None:
    path = tmp_path / "t.v"
    path.write_text("x", encoding="utf-8")
    app = create_test_app(path, cast(RocqCursor, _StubCursorEmpty()))
    transport = httpx.ASGITransport(app=app)
    async with httpx.AsyncClient(transport=transport, base_url="http://test") as client:
        response = await client.get("/feedback", params={"line": 0, "character": 0})
    assert response.status_code == 200
    body = response.json()
    assert body["status"] == "ok"
    assert body["feedback_messages"] == []


@pytest.mark.asyncio
async def test_feedback_bad_line_via_asgi() -> None:
    fixture = Path(__file__).resolve().parent / "fixtures" / "minimal.v"
    app = create_test_app(fixture, cast(RocqCursor, _StubCursorEmpty()))
    transport = httpx.ASGITransport(app=app)
    async with httpx.AsyncClient(transport=transport, base_url="http://test") as client:
        response = await client.get("/feedback", params={"line": 50, "character": 0})
    assert response.status_code == 400


@pytest.mark.asyncio
async def test_health_via_asgi(tmp_path: Path) -> None:
    path = tmp_path / "t.v"
    path.write_text("x", encoding="utf-8")
    app = create_test_app(path, cast(RocqCursor, _StubCursorEmpty()))
    transport = httpx.ASGITransport(app=app)
    async with httpx.AsyncClient(transport=transport, base_url="http://test") as client:
        response = await client.get("/health")
    assert response.status_code == 200
    assert response.json() == {"status": "ok"}
