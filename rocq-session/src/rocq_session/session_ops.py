"""Session operations beyond feedback/reload (cursor/query/insert)."""

from __future__ import annotations

import asyncio
import logging
from typing import Literal, TypedDict

from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

from .feedback import FeedbackCache
from .position import lsp_position_to_byte_offset

logger = logging.getLogger(__name__)


class CursorPayload(TypedDict):
    status: Literal["ok"]
    index: int


class QueryOkPayload(TypedDict):
    status: Literal["ok"]
    index: int
    command_data: dict[str, object]


class QueryErrPayload(TypedDict):
    status: Literal["error"]
    message: str


class InsertOkPayload(TypedDict):
    status: Literal["ok"]
    index: int
    command_data: dict[str, object]


class InsertErrPayload(TypedDict):
    status: Literal["error"]
    message: str
    feedback_messages: list[dict[str, object]]
    error_loc: dict[str, object] | None


QueryPayload = QueryOkPayload | QueryErrPayload
InsertPayload = InsertOkPayload | InsertErrPayload


def _reset_feedback_cache(cache: FeedbackCache) -> None:
    """Invalidate cache after live cursor/document mutations."""
    cache.commands.clear()
    cache.processed_extent = 0
    cache.terminal = None
    cache.initialized = False


def _dump_feedback_messages(
    messages: list[rdm_api.FeedbackMessage],
) -> list[dict[str, object]]:
    return [m.model_dump() for m in messages]


def _dump_error_loc(loc: rdm_api.RocqLoc | None) -> dict[str, object] | None:
    return None if loc is None else loc.model_dump()


def _command_error_payload(message: str, err: rdm_api.CommandError | None) -> InsertErrPayload:
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


async def cursor_location(
    cursor: RocqCursor,
    session_lock: asyncio.Lock,
) -> CursorPayload:
    async with session_lock:
        return {"status": "ok", "index": await cursor.cursor_index()}


def _index_from_byte_offset(
    items: list[rdm_api.PrefixItem | rdm_api.SuffixItem],
    target_byte: int,
) -> int:
    visible_off = 0
    for i, item in enumerate(items):
        if item.kind == "ghost":
            continue
        item_len = len(item.text.encode("utf-8"))
        end = visible_off + item_len
        if visible_off <= target_byte < end:
            return i
        visible_off = end
    if target_byte == visible_off:
        return len(items)
    raise ValueError("Position is past end of document")


async def _index_from_lsp_position(
    cursor: RocqCursor,
    line: int,
    character: int,
) -> int:
    prefix = await cursor.doc_prefix()
    suffix = await cursor.doc_suffix()
    items: list[rdm_api.PrefixItem | rdm_api.SuffixItem] = [*prefix, *suffix]
    source = "".join(item.text for item in items if item.kind != "ghost")
    target_byte = lsp_position_to_byte_offset(source, line, character)
    return _index_from_byte_offset(items, target_byte)


async def run_query(
    cursor: RocqCursor,
    cache: FeedbackCache,
    session_lock: asyncio.Lock,
    *,
    text: str,
    line: int | None,
    character: int | None,
) -> QueryPayload:
    async with session_lock:
        current = await cursor.cursor_index()
        if line is None and character is None:
            target = current
        elif line is None or character is None:
            return _command_error_payload(
                "line and character must either both be set or both be omitted",
                None,
            )
        else:
            try:
                target = await _index_from_lsp_position(cursor, line, character)
            except ValueError as exc:
                return _command_error_payload(str(exc), None)
        if target < current:
            clone = await cursor.clone(materialize=True)
            try:
                reset = await clone.go_to(0)
                if isinstance(reset, rdm_api.Err):
                    return {"status": "error", "message": reset.message}
                if target > 0:
                    advanced = await clone.advance_to(target)
                    if isinstance(advanced, rdm_api.Err):
                        return {"status": "error", "message": advanced.message}
                query = await clone.query(text)
            finally:
                try:
                    await clone.dispose()
                except Exception as exc:
                    logger.warning("Failed disposing query clone: %s", exc)
        else:
            if target > current:
                advanced = await cursor.advance_to(target)
                if isinstance(advanced, rdm_api.Err):
                    return {"status": "error", "message": advanced.message}
                _reset_feedback_cache(cache)
            query = await cursor.query(text)
        if isinstance(query, rdm_api.Err):
            return {"status": "error", "message": query.message}
        return {"status": "ok", "index": target, "command_data": query.model_dump()}


async def insert_command(
    cursor: RocqCursor,
    cache: FeedbackCache,
    session_lock: asyncio.Lock,
    *,
    text: str,
    line: int | None,
    character: int | None,
) -> InsertPayload:
    async with session_lock:
        current = await cursor.cursor_index()
        if line is None and character is None:
            target = current
        elif line is None or character is None:
            return _command_error_payload(
                "line and character must either both be set or both be omitted",
                None,
            )
        else:
            try:
                target = await _index_from_lsp_position(cursor, line, character)
            except ValueError as exc:
                return _command_error_payload(str(exc), None)
        moved = await cursor.go_to(target)
        if isinstance(moved, rdm_api.Err):
            err = moved.data if isinstance(moved.data, rdm_api.CommandError) else None
            return _command_error_payload(moved.message, err)

        result = await cursor.insert_command(text)
        if isinstance(result, rdm_api.Err):
            return _command_error_payload(result.message, result.data)

        _reset_feedback_cache(cache)
        return {
            "status": "ok",
            "index": await cursor.cursor_index(),
            "command_data": result.model_dump(),
        }
