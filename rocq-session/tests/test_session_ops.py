"""Tests for cursor/query/insert session operations."""

from __future__ import annotations

import asyncio
from dataclasses import dataclass, field
from typing import cast

import pytest
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_session.feedback import CachedCommand, FeedbackCache
from rocq_session.session_ops import cursor_location, insert_command, run_query


def _mk_command_data() -> rdm_api.CommandData:
    return rdm_api.CommandData(synterp_ast=rdm_api.VernacData(kind="Noop"))


@dataclass
class _CloneCursor:
    parent: _FakeCursor
    index: int = 0
    disposed: bool = False

    async def go_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        self.index = index
        self.parent.clone_go_to_calls.append(index)
        return None

    async def advance_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        self.index = index
        self.parent.clone_advance_to_calls.append(index)
        return None

    async def query(self, text: str) -> rdm_api.CommandData | rdm_api.Err[None]:
        self.parent.clone_query_calls.append((self.index, text))
        return _mk_command_data()

    async def dispose(self) -> None:
        self.disposed = True
        self.parent.clone_dispose_calls += 1


@dataclass
class _FakeCursor:
    index: int = 0
    prefix: list[rdm_api.PrefixItem] = field(default_factory=list)
    suffix: list[rdm_api.SuffixItem] = field(default_factory=list)
    go_to_calls: list[int] = field(default_factory=list)
    advance_to_calls: list[int] = field(default_factory=list)
    query_calls: list[tuple[int, str]] = field(default_factory=list)
    insert_calls: list[tuple[int, str]] = field(default_factory=list)
    clone_materialize_flags: list[bool] = field(default_factory=list)
    clone_go_to_calls: list[int] = field(default_factory=list)
    clone_advance_to_calls: list[int] = field(default_factory=list)
    clone_query_calls: list[tuple[int, str]] = field(default_factory=list)
    clone_dispose_calls: int = 0

    async def cursor_index(self) -> int:
        return self.index

    async def go_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        self.go_to_calls.append(index)
        self.index = index
        return None

    async def advance_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        self.advance_to_calls.append(index)
        self.index = index
        return None

    async def query(self, text: str) -> rdm_api.CommandData | rdm_api.Err[None]:
        self.query_calls.append((self.index, text))
        return _mk_command_data()

    async def doc_prefix(self) -> list[rdm_api.PrefixItem]:
        return list(self.prefix)

    async def doc_suffix(self) -> list[rdm_api.SuffixItem]:
        return list(self.suffix)

    async def insert_command(
        self, text: str, blanks: str | None = "\n", ghost: bool = False
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        self.insert_calls.append((self.index, text))
        self.index += 1
        return _mk_command_data()

    async def clone(self, *, materialize: bool = False) -> _CloneCursor:
        self.clone_materialize_flags.append(materialize)
        return _CloneCursor(self, index=self.index)


@pytest.mark.asyncio
async def test_cursor_location_reports_current_index() -> None:
    c = _FakeCursor(index=3)
    payload = await cursor_location(cast(RocqCursor, c), asyncio.Lock())
    assert payload == {"status": "ok", "index": 3}


@pytest.mark.asyncio
async def test_query_default_uses_current_cursor() -> None:
    c = _FakeCursor(index=4)
    cache = FeedbackCache(
        commands=[CachedCommand(offset=0, byte_end=1, feedback_messages=[])],
        processed_extent=10,
        initialized=True,
    )
    out = await run_query(
        cast(RocqCursor, c),
        cache,
        asyncio.Lock(),
        text="About nat.",
        line=None,
        character=None,
    )
    assert out["status"] == "ok"
    assert out["index"] == 4
    assert c.query_calls == [(4, "About nat.")]
    assert c.clone_materialize_flags == []
    # No live cursor movement => cache remains untouched.
    assert cache.initialized
    assert cache.processed_extent == 10


@pytest.mark.asyncio
async def test_query_before_current_uses_clone_materialized() -> None:
    c = _FakeCursor(index=7)
    cache = FeedbackCache(initialized=True, processed_extent=100)
    out = await run_query(
        cast(RocqCursor, c),
        cache,
        asyncio.Lock(),
        text="About nat.",
        line=0,
        character=0,
    )
    assert out["status"] == "ok"
    assert out["index"] == 0
    assert c.clone_materialize_flags == [True]
    assert c.clone_go_to_calls == [0]
    assert c.clone_advance_to_calls == []
    assert c.clone_query_calls == [(0, "About nat.")]
    assert c.clone_dispose_calls == 1
    assert c.index == 7
    assert c.query_calls == []
    # Live state unchanged => cache unchanged.
    assert cache.initialized
    assert cache.processed_extent == 100


@pytest.mark.asyncio
async def test_query_after_current_advances_live_and_resets_cache() -> None:
    c = _FakeCursor(
        index=1,
        prefix=[
            rdm_api.PrefixItem(text="A.", offset=0, kind="command", data=None),
        ],
        suffix=[
            rdm_api.SuffixItem(text="\n", kind="blanks", data=None),
            rdm_api.SuffixItem(text="B.", kind="command", data=None),
            rdm_api.SuffixItem(text="\n", kind="blanks", data=None),
        ],
    )
    cache = FeedbackCache(
        commands=[CachedCommand(offset=0, byte_end=5, feedback_messages=[])],
        processed_extent=5,
        terminal={
            "status": "error",
            "message": "stale",
            "feedback_messages": [],
            "error_loc": None,
        },
        initialized=True,
    )
    out = await run_query(
        cast(RocqCursor, c),
        cache,
        asyncio.Lock(),
        text="About nat.",
        line=1,
        character=0,
    )
    assert out["status"] == "ok"
    assert c.advance_to_calls == [2]
    assert c.query_calls == [(2, "About nat.")]
    assert cache.commands == []
    assert cache.processed_extent == 0
    assert cache.terminal is None
    assert not cache.initialized


@pytest.mark.asyncio
async def test_insert_default_at_current_resets_cache() -> None:
    c = _FakeCursor(index=2)
    cache = FeedbackCache(
        commands=[CachedCommand(offset=0, byte_end=5, feedback_messages=[])],
        processed_extent=5,
        initialized=True,
    )
    out = await insert_command(
        cast(RocqCursor, c),
        cache,
        asyncio.Lock(),
        text="Check nat.",
        line=None,
        character=None,
    )
    assert out["status"] == "ok"
    assert c.go_to_calls == [2]
    assert c.insert_calls == [(2, "Check nat.")]
    assert out["index"] == 3
    assert cache.commands == []
    assert cache.processed_extent == 0
    assert not cache.initialized


@pytest.mark.asyncio
async def test_insert_with_lsp_position_uses_mapped_index() -> None:
    c = _FakeCursor(
        index=0,
        prefix=[],
        suffix=[
            rdm_api.SuffixItem(text="A.", kind="command", data=None),
            rdm_api.SuffixItem(text="\n", kind="blanks", data=None),
        ],
    )
    cache = FeedbackCache(initialized=True)
    out = await insert_command(
        cast(RocqCursor, c),
        cache,
        asyncio.Lock(),
        text="Check nat.",
        line=0,
        character=0,
    )
    assert out["status"] == "ok"
    assert c.go_to_calls == [0]
