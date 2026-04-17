"""Tests for ``rocq_session.reload``."""

from __future__ import annotations

import asyncio
from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal, cast

import pytest
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_session.feedback import CachedCommand, FeedbackCache
from rocq_session.reload import _find_divergence_index, reload_file

PrefixKind = Literal["blanks", "command", "ghost"]
SentenceKind = Literal["blanks", "command"]


def _pi(text: str, offset: int, kind: PrefixKind) -> rdm_api.PrefixItem:
    return rdm_api.PrefixItem(text=text, offset=offset, kind=kind, data=None)


def _sent(text: str, kind: SentenceKind) -> rdm_api.Sentence:
    return rdm_api.Sentence(text=text, kind=kind, data=None)


def _fb(text: str) -> rdm_api.FeedbackMessage:
    return rdm_api.FeedbackMessage(text=text, quickfix=[], loc=None, level="info")


@dataclass
class FakeReloadCursor:
    """Document-cursor stub sufficient for exercising ``reload_file``."""

    prefix: list[rdm_api.PrefixItem] = field(default_factory=list)
    parse_result: (
        list[rdm_api.Sentence] | rdm_api.Err[rdm_api.SentenceSplitError] | None
    ) = None
    clone_go_to_result: rdm_api.Err[rdm_api.CommandError | None] | None = None
    replace_suffix_result: (
        list[rdm_api.Sentence] | rdm_api.Err[rdm_api.SentenceSplitError] | None
    ) = None

    # Recorded calls
    clone_calls: int = 0
    clone_materialize_flags: list[bool] = field(default_factory=list)
    clone_dispose_count: int = 0
    clone_go_to_calls: list[int] = field(default_factory=list)
    clone_replace_suffix_calls: list[str] = field(default_factory=list)
    revert_calls: list[tuple[bool, int]] = field(default_factory=list)
    replace_suffix_calls: list[str] = field(default_factory=list)

    async def doc_prefix(self) -> list[rdm_api.PrefixItem]:
        return list(self.prefix)

    async def revert_before(self, erase: bool, index: int) -> None | rdm_api.Err[None]:
        self.revert_calls.append((erase, index))
        self.prefix = self.prefix[:index]
        return None

    async def replace_suffix(
        self, text: str
    ) -> list[rdm_api.Sentence] | rdm_api.Err[rdm_api.SentenceSplitError]:
        self.replace_suffix_calls.append(text)
        if self.replace_suffix_result is None:
            return []
        return self.replace_suffix_result

    async def clone(self, *, materialize: bool = False) -> FakeReloadCursor:
        self.clone_calls += 1
        self.clone_materialize_flags.append(materialize)
        parent = self

        class _Clone:
            async def go_to(
                self_inner, index: int
            ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
                parent.clone_go_to_calls.append(index)
                return parent.clone_go_to_result

            async def replace_suffix(
                self_inner, text: str
            ) -> list[rdm_api.Sentence] | rdm_api.Err[rdm_api.SentenceSplitError]:
                parent.clone_replace_suffix_calls.append(text)
                assert parent.parse_result is not None
                return parent.parse_result

            async def dispose(self_inner) -> None:
                parent.clone_dispose_count += 1

        return cast(FakeReloadCursor, _Clone())


def test_divergence_empty_prefix() -> None:
    assert _find_divergence_index([], [_sent("Check nat.", "command")]) == (0, 0)


def test_divergence_full_match() -> None:
    prefix = [_pi("Check nat.", 0, "command")]
    sents = [_sent("Check nat.", "command"), _sent("\n", "blanks")]
    assert _find_divergence_index(prefix, sents) == (1, 1)


def test_divergence_partial() -> None:
    prefix = [
        _pi("Check nat.", 0, "command"),
        _pi("\n", 10, "blanks"),
        _pi("Check bool.", 11, "command"),
    ]
    sents = [
        _sent("Check nat.", "command"),
        _sent("\n", "blanks"),
        _sent("Check int.", "command"),
    ]
    assert _find_divergence_index(prefix, sents) == (2, 2)


def test_divergence_ghost_preserved() -> None:
    # Ghost items don't appear in the file; they should be skipped.
    prefix = [
        _pi("Check nat.", 0, "command"),
        _pi("Unshelve.", 10, "ghost"),
        _pi("\n", 10, "blanks"),
        _pi("Check bool.", 11, "command"),
    ]
    sents = [
        _sent("Check nat.", "command"),
        _sent("\n", "blanks"),
        _sent("Check bool.", "command"),
    ]
    assert _find_divergence_index(prefix, sents) == (4, 3)


def test_divergence_file_shorter() -> None:
    prefix = [
        _pi("Check nat.", 0, "command"),
        _pi("\n", 10, "blanks"),
        _pi("Check bool.", 11, "command"),
    ]
    sents = [_sent("Check nat.", "command")]
    assert _find_divergence_index(prefix, sents) == (1, 1)


@pytest.mark.asyncio
async def test_reload_full_match_keeps_cache(tmp_path: Path) -> None:
    cmd1 = _pi("Check nat.", 0, "command")
    blank = _pi("\n", 10, "blanks")
    cursor = FakeReloadCursor(
        prefix=[cmd1, blank],
        parse_result=[
            _sent("Check nat.", "command"),
            _sent("\n", "blanks"),
            _sent("Check bool.", "command"),
        ],
    )
    cache = FeedbackCache(
        commands=[CachedCommand(offset=0, byte_end=10, feedback_messages=[_fb("fb1")])],
        processed_extent=11,
        initialized=True,
    )
    file_path = tmp_path / "f.v"
    file_path.write_text("Check nat.\nCheck bool.", encoding="utf-8")

    result = await reload_file(
        cast(RocqCursor, cursor), cache, asyncio.Lock(), file_path
    )

    assert result["status"] == "ok"
    assert result["prefix_items_preserved"] == 2
    assert result["prefix_items_reverted"] == 0
    assert result["cached_commands_kept"] == 1
    assert result["cached_commands_dropped"] == 0
    assert cursor.revert_calls == []
    assert cursor.replace_suffix_calls == ["Check bool."]
    assert cache.processed_extent == 11
    assert cache.terminal is None
    assert cursor.clone_dispose_count == 1


@pytest.mark.asyncio
async def test_reload_partial_divergence_drops_invalid_cache(
    tmp_path: Path,
) -> None:
    cmd1 = _pi("Check nat.", 0, "command")
    blank = _pi("\n", 10, "blanks")
    cmd2 = _pi("Check bool.", 11, "command")
    cursor = FakeReloadCursor(
        prefix=[cmd1, blank, cmd2],
        parse_result=[
            _sent("Check nat.", "command"),
            _sent("\n", "blanks"),
            _sent("Check int.", "command"),
        ],
    )
    cache = FeedbackCache(
        commands=[
            CachedCommand(offset=0, byte_end=10, feedback_messages=[_fb("fb1")]),
            CachedCommand(offset=11, byte_end=22, feedback_messages=[_fb("fb2")]),
        ],
        processed_extent=22,
        terminal={
            "status": "error",
            "message": "old error",
            "feedback_messages": [],
            "error_loc": None,
        },
        initialized=True,
    )
    file_path = tmp_path / "f.v"
    file_path.write_text("Check nat.\nCheck int.", encoding="utf-8")

    result = await reload_file(
        cast(RocqCursor, cursor), cache, asyncio.Lock(), file_path
    )

    assert result["status"] == "ok"
    assert result["prefix_items_preserved"] == 2
    assert result["prefix_items_reverted"] == 1
    assert result["cached_commands_kept"] == 1
    assert result["cached_commands_dropped"] == 1
    assert cursor.revert_calls == [(True, 2)]
    assert cursor.replace_suffix_calls == ["Check int."]
    assert [c.offset for c in cache.commands] == [0]
    assert cache.terminal is None
    assert cache.processed_extent == 11


@pytest.mark.asyncio
async def test_reload_completely_different_clears_cache(tmp_path: Path) -> None:
    cmd1 = _pi("Check nat.", 0, "command")
    cursor = FakeReloadCursor(
        prefix=[cmd1],
        parse_result=[_sent("Check bool.", "command")],
    )
    cache = FeedbackCache(
        commands=[CachedCommand(offset=0, byte_end=10, feedback_messages=[_fb("fb1")])],
        processed_extent=10,
        initialized=True,
    )
    file_path = tmp_path / "f.v"
    file_path.write_text("Check bool.", encoding="utf-8")

    result = await reload_file(
        cast(RocqCursor, cursor), cache, asyncio.Lock(), file_path
    )

    assert result["status"] == "ok"
    assert result["prefix_items_reverted"] == 1
    assert cursor.revert_calls == [(True, 0)]
    assert cursor.replace_suffix_calls == ["Check bool."]
    assert cache.commands == []
    assert cache.processed_extent == 0


@pytest.mark.asyncio
async def test_reload_missing_file_returns_error(tmp_path: Path) -> None:
    cursor = FakeReloadCursor()
    cache = FeedbackCache()
    missing = tmp_path / "nope.v"

    result = await reload_file(cast(RocqCursor, cursor), cache, asyncio.Lock(), missing)
    assert result["status"] == "error"
    assert "not found" in result["message"].lower()
    assert cursor.clone_calls == 0
    assert cursor.revert_calls == []


@pytest.mark.asyncio
async def test_reload_parse_error_leaves_state_untouched(tmp_path: Path) -> None:
    cmd1 = _pi("Check nat.", 0, "command")
    cursor = FakeReloadCursor(
        prefix=[cmd1],
        parse_result=rdm_api.Err[rdm_api.SentenceSplitError](
            "syntax error",
            rdm_api.SentenceSplitError(rest="garbage", sentences=[]),
        ),
    )
    cache = FeedbackCache(
        commands=[CachedCommand(offset=0, byte_end=10, feedback_messages=[_fb("fb1")])],
        processed_extent=10,
        initialized=True,
    )
    file_path = tmp_path / "f.v"
    file_path.write_text("garbage", encoding="utf-8")

    result = await reload_file(
        cast(RocqCursor, cursor), cache, asyncio.Lock(), file_path
    )

    assert result["status"] == "error"
    assert "syntax error" in result["message"]
    assert cursor.revert_calls == []
    assert cursor.replace_suffix_calls == []
    assert cache.commands  # untouched
    assert cache.processed_extent == 10
    assert cursor.clone_dispose_count == 1
