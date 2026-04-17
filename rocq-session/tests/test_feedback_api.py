"""HTTP tests for ``/feedback`` using ``httpx.ASGITransport``."""

from __future__ import annotations

from pathlib import Path
from typing import cast

import httpx
import pytest
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_session.testing import create_test_app


class _StubCloneCursor:
    async def advance_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        return None

    async def go_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        return None

    async def query(self, text: str) -> rdm_api.CommandData | rdm_api.Err[None]:
        return rdm_api.CommandData(synterp_ast=rdm_api.VernacData(kind="Noop"))

    async def replace_suffix(
        self, text: str
    ) -> list[rdm_api.Sentence] | rdm_api.Err[rdm_api.SentenceSplitError]:
        return []

    async def dispose(self) -> None:
        return None


class _StubCursorEmpty:
    """Minimal cursor: empty document, nothing to step."""

    _index: int = 0

    async def advance_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        self._index = index
        return None

    async def cursor_index(self) -> int:
        return self._index

    async def go_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        self._index = index
        return None

    async def has_suffix(self) -> bool:
        return False

    async def run_step(
        self,
    ) -> rdm_api.CommandData | None | rdm_api.Err[rdm_api.CommandError]:
        raise AssertionError("run_step should not be called")

    async def doc_prefix(self) -> list[rdm_api.PrefixItem]:
        return []

    async def clone(self, *, materialize: bool = False) -> _StubCloneCursor:
        return _StubCloneCursor()

    async def replace_suffix(
        self, text: str
    ) -> list[rdm_api.Sentence] | rdm_api.Err[rdm_api.SentenceSplitError]:
        return []

    async def revert_before(self, erase: bool, index: int) -> None | rdm_api.Err[None]:
        self._index = index
        return None

    async def query(self, text: str) -> rdm_api.CommandData | rdm_api.Err[None]:
        return rdm_api.CommandData(synterp_ast=rdm_api.VernacData(kind="Noop"))

    async def insert_command(
        self, text: str, blanks: str | None = "\n", ghost: bool = False
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        self._index += 1
        return rdm_api.CommandData(synterp_ast=rdm_api.VernacData(kind="Noop"))


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


@pytest.mark.asyncio
async def test_cursor_via_asgi(tmp_path: Path) -> None:
    path = tmp_path / "t.v"
    path.write_text("x", encoding="utf-8")
    app = create_test_app(path, cast(RocqCursor, _StubCursorEmpty()))
    transport = httpx.ASGITransport(app=app)
    async with httpx.AsyncClient(transport=transport, base_url="http://test") as client:
        response = await client.get("/cursor")
    assert response.status_code == 200
    assert response.json() == {"status": "ok", "index": 0}


@pytest.mark.asyncio
async def test_query_via_asgi(tmp_path: Path) -> None:
    path = tmp_path / "t.v"
    path.write_text("x", encoding="utf-8")
    app = create_test_app(path, cast(RocqCursor, _StubCursorEmpty()))
    transport = httpx.ASGITransport(app=app)
    async with httpx.AsyncClient(transport=transport, base_url="http://test") as client:
        response = await client.post("/query", json={"text": "About nat."})
    assert response.status_code == 200
    payload = response.json()
    assert payload["status"] == "ok"
    assert payload["index"] == 0


@pytest.mark.asyncio
async def test_insert_via_asgi(tmp_path: Path) -> None:
    path = tmp_path / "t.v"
    path.write_text("x", encoding="utf-8")
    app = create_test_app(path, cast(RocqCursor, _StubCursorEmpty()))
    transport = httpx.ASGITransport(app=app)
    async with httpx.AsyncClient(transport=transport, base_url="http://test") as client:
        response = await client.post("/insert", json={"text": "Check nat."})
    assert response.status_code == 200
    payload = response.json()
    assert payload["status"] == "ok"
    assert payload["index"] == 1


@pytest.mark.asyncio
async def test_quit_triggers_callback(tmp_path: Path) -> None:
    path = tmp_path / "t.v"
    path.write_text("x", encoding="utf-8")
    called: list[int] = []

    def on_shutdown() -> None:
        called.append(1)

    app = create_test_app(
        path, cast(RocqCursor, _StubCursorEmpty()), request_shutdown=on_shutdown
    )
    transport = httpx.ASGITransport(app=app)
    async with httpx.AsyncClient(transport=transport, base_url="http://test") as client:
        response = await client.post("/quit")
    assert response.status_code == 202
    assert response.json() == {"status": "shutting_down"}
    assert called == [1]


@pytest.mark.asyncio
async def test_reload_via_asgi(tmp_path: Path) -> None:
    path = tmp_path / "t.v"
    path.write_text("", encoding="utf-8")
    app = create_test_app(path, cast(RocqCursor, _StubCursorEmpty()))
    transport = httpx.ASGITransport(app=app)
    async with httpx.AsyncClient(transport=transport, base_url="http://test") as client:
        response = await client.post("/reload")
    assert response.status_code == 200
    body = response.json()
    assert body["status"] == "ok"
    assert body["prefix_items_preserved"] == 0
    assert body["prefix_items_reverted"] == 0


@pytest.mark.asyncio
async def test_reload_missing_file_via_asgi(tmp_path: Path) -> None:
    missing = tmp_path / "does-not-exist.v"
    app = create_test_app(missing, cast(RocqCursor, _StubCursorEmpty()))
    transport = httpx.ASGITransport(app=app)
    async with httpx.AsyncClient(transport=transport, base_url="http://test") as client:
        response = await client.post("/reload")
    assert response.status_code == 200
    body = response.json()
    assert body["status"] == "error"
    assert "not found" in body["message"].lower()


@pytest.mark.asyncio
async def test_quit_without_shutdown_hook_503(tmp_path: Path) -> None:
    path = tmp_path / "t.v"
    path.write_text("x", encoding="utf-8")
    app = create_test_app(path, cast(RocqCursor, _StubCursorEmpty()))
    transport = httpx.ASGITransport(app=app)
    async with httpx.AsyncClient(transport=transport, base_url="http://test") as client:
        response = await client.post("/quit")
    assert response.status_code == 503
