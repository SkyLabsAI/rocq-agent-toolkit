"""Collect Rocq feedback for a UTF-8 byte offset using a Rocq cursor.

The server caches feedback for every command as it is processed. Requests
reuse the cursor's forward progress across calls and only step further when
the target byte is past the currently processed region.
"""

from __future__ import annotations

import asyncio
from dataclasses import dataclass, field
from typing import Literal, TypedDict

from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api


def processed_byte_length(prefix: list[rdm_api.PrefixItem]) -> int:
    """Match RDM cursor_off: sum UTF-8 byte lengths of non-ghost processed items."""
    return sum(
        len(item.text.encode("utf-8")) for item in prefix if item.kind != "ghost"
    )


class FeedbackOkPayload(TypedDict):
    status: Literal["ok"]
    feedback_messages: list[dict[str, object]]


class FeedbackErrPayload(TypedDict):
    status: Literal["error"]
    message: str
    feedback_messages: list[dict[str, object]]
    error_loc: dict[str, object] | None


FeedbackPayload = FeedbackOkPayload | FeedbackErrPayload


@dataclass(frozen=True)
class CachedCommand:
    """Single processed command with the feedback it produced."""

    offset: int
    byte_end: int
    feedback_messages: list[rdm_api.FeedbackMessage]


@dataclass
class FeedbackCache:
    """Feedback cache tracking the cursor's processed region.

    Invariants:
    - ``commands`` holds, in source order, every ``command`` prefix item that
      has been processed, with the feedback emitted when stepping it.
    - ``processed_extent`` equals ``processed_byte_length`` of the cursor's
      doc prefix at the last observation; all source bytes ``< processed_extent``
      have been processed.
    - ``terminal`` is sticky: once the cursor reports EOF or an error while
      advancing, it holds the canonical response for positions past the
      processed region.
    - ``initialized`` flips to True after the first ``cursor.go_to(0)``.
    """

    commands: list[CachedCommand] = field(default_factory=list)
    processed_extent: int = 0
    terminal: FeedbackErrPayload | None = None
    initialized: bool = False

    def find_containing_command(self, target_byte: int) -> CachedCommand | None:
        for cmd in self.commands:
            if cmd.offset <= target_byte < cmd.byte_end:
                return cmd
        return None


def _dump_feedback_messages(
    messages: list[rdm_api.FeedbackMessage],
) -> list[dict[str, object]]:
    return [m.model_dump() for m in messages]


def _dump_error_loc(loc: rdm_api.RocqLoc | None) -> dict[str, object] | None:
    if loc is None:
        return None
    return loc.model_dump()


def _err_payload_from_cmd_error(
    message: str, err: rdm_api.CommandError | None
) -> FeedbackErrPayload:
    if err is None:
        return {
            "status": "error",
            "message": message,
            "feedback_messages": [],
            "error_loc": None,
        }
    return {
        "status": "error",
        "message": message,
        "feedback_messages": _dump_feedback_messages(err.feedback_messages),
        "error_loc": _dump_error_loc(err.error_loc),
    }


def _ok_payload(
    messages: list[rdm_api.FeedbackMessage],
) -> FeedbackOkPayload:
    return {
        "status": "ok",
        "feedback_messages": _dump_feedback_messages(messages),
    }


def select_feedback_messages(
    prefix: list[rdm_api.PrefixItem],
    target_byte: int,
    feedback_by_command_offset: dict[int, list[rdm_api.FeedbackMessage]],
) -> list[rdm_api.FeedbackMessage]:
    """Return feedback for the last processed command whose UTF-8 span contains ``target_byte``."""
    match_offset: int | None = None
    for item in prefix:
        if item.kind != "command":
            continue
        end = item.offset + len(item.text.encode("utf-8"))
        if item.offset <= target_byte < end:
            match_offset = item.offset
    if match_offset is None:
        return []
    return list(feedback_by_command_offset.get(match_offset, []))


async def _initialize_cursor(cursor: RocqCursor, cache: FeedbackCache) -> None:
    """Reset the cursor to the start of the document once per cache."""
    go = await cursor.go_to(0)
    if isinstance(go, rdm_api.Err):
        err_data = go.data if isinstance(go.data, rdm_api.CommandError) else None
        cache.terminal = _err_payload_from_cmd_error(go.message, err_data)
    cache.initialized = True


async def _advance_to(
    cursor: RocqCursor,
    cache: FeedbackCache,
    target_byte: int,
) -> None:
    """Step the cursor forward, appending to the cache, until past ``target_byte``.

    Stops early if the cache is already terminal, the document has no more
    content, or a step errors.
    """
    while cache.terminal is None and cache.processed_extent < target_byte:
        if not await cursor.has_suffix():
            cache.terminal = {
                "status": "error",
                "message": "Position is past the end of the processed document",
                "feedback_messages": [],
                "error_loc": None,
            }
            return
        step = await cursor.run_step()
        if isinstance(step, rdm_api.Err):
            err_data = (
                step.data if isinstance(step.data, rdm_api.CommandError) else None
            )
            cache.terminal = _err_payload_from_cmd_error(step.message, err_data)
            return
        prefix = await cursor.doc_prefix()
        cache.processed_extent = processed_byte_length(prefix)
        if (
            isinstance(step, rdm_api.CommandData)
            and prefix
            and prefix[-1].kind == "command"
        ):
            last = prefix[-1]
            byte_len = len(last.text.encode("utf-8"))
            cache.commands.append(
                CachedCommand(
                    offset=last.offset,
                    byte_end=last.offset + byte_len,
                    feedback_messages=step.feedback_messages,
                )
            )


async def feedback_at_byte(
    cursor: RocqCursor,
    target_byte: int,
    cache: FeedbackCache,
    session_lock: asyncio.Lock,
) -> FeedbackPayload:
    """Return feedback for ``target_byte``, using and updating ``cache``.

    If ``target_byte`` lies within the already-processed region, the answer
    is served from the cache without advancing the cursor. Otherwise the
    cursor is advanced (and the cache is extended) until the target is
    covered, the document is exhausted, or a command errors.
    """
    async with session_lock:
        if not cache.initialized:
            await _initialize_cursor(cursor, cache)

        if cache.terminal is not None and not cache.commands:
            return cache.terminal

        if cache.processed_extent < target_byte and cache.terminal is None:
            await _advance_to(cursor, cache, target_byte)

        if cache.processed_extent < target_byte and cache.terminal is not None:
            return cache.terminal

        cmd = cache.find_containing_command(target_byte)
        return _ok_payload(cmd.feedback_messages if cmd else [])
