"""Collect Rocq feedback for a UTF-8 byte offset using a Rocq cursor."""

from __future__ import annotations

import asyncio
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


def _dump_feedback_messages(
    messages: list[rdm_api.FeedbackMessage],
) -> list[dict[str, object]]:
    return [m.model_dump() for m in messages]


def _dump_error_loc(loc: rdm_api.RocqLoc | None) -> dict[str, object] | None:
    if loc is None:
        return None
    return loc.model_dump()


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


async def feedback_at_byte(
    cursor: RocqCursor,
    target_byte: int,
    session_lock: asyncio.Lock,
) -> FeedbackPayload:
    """Reset the document, step until ``processed_byte_length >= target_byte``, then resolve feedback."""
    async with session_lock:
        go = await cursor.go_to(0)
        if isinstance(go, rdm_api.Err):
            err_data = go.data
            if isinstance(err_data, rdm_api.CommandError):
                return {
                    "status": "error",
                    "message": go.message,
                    "feedback_messages": _dump_feedback_messages(
                        err_data.feedback_messages
                    ),
                    "error_loc": _dump_error_loc(err_data.error_loc),
                }
            return {
                "status": "error",
                "message": go.message,
                "feedback_messages": [],
                "error_loc": None,
            }

        feedback_by_command_offset: dict[int, list[rdm_api.FeedbackMessage]] = {}

        while processed_byte_length(await cursor.doc_prefix()) < target_byte:
            if not await cursor.has_suffix():
                return {
                    "status": "error",
                    "message": "Position is past the end of the processed document",
                    "feedback_messages": [],
                    "error_loc": None,
                }
            step = await cursor.run_step()
            if isinstance(step, rdm_api.Err):
                err_data = step.data
                assert isinstance(err_data, rdm_api.CommandError)
                return {
                    "status": "error",
                    "message": step.message,
                    "feedback_messages": _dump_feedback_messages(
                        err_data.feedback_messages
                    ),
                    "error_loc": _dump_error_loc(err_data.error_loc),
                }
            prefix = await cursor.doc_prefix()
            last = prefix[-1]
            if isinstance(step, rdm_api.CommandData) and last.kind == "command":
                feedback_by_command_offset[last.offset] = step.feedback_messages

        prefix = await cursor.doc_prefix()
        msgs = select_feedback_messages(
            prefix, target_byte, feedback_by_command_offset
        )
        return {"status": "ok", "feedback_messages": _dump_feedback_messages(msgs)}
