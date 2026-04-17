"""Reload the Rocq document from disk, reusing the unchanged processed prefix.

The reload flow:

1. Read the file from disk.
2. Parse it (via a materialized clone of the session cursor, reverted to 0,
   on which we call ``replace_suffix``). This yields the file's sentences
   without touching the live cursor.
3. Walk the live cursor's prefix against the file's sentences to find the
   first divergence. Ghost items are preserved (they don't exist in the file).
4. Revert the live cursor to that divergence index (with ``erase=True``),
   dropping the invalidated processed items.
5. Call ``replace_suffix`` on the live cursor with the remaining file text,
   installing the new suffix.
6. Drop all cached command feedback that corresponds to reverted items and
   clear any sticky terminal state in the cache.
"""

from __future__ import annotations

import asyncio
import logging
from pathlib import Path
from typing import Literal, TypedDict

from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

from .feedback import CachedCommand, FeedbackCache, processed_byte_length

logger = logging.getLogger(__name__)


class ReloadOkPayload(TypedDict):
    status: Literal["ok"]
    prefix_items_preserved: int
    prefix_items_reverted: int
    cached_commands_kept: int
    cached_commands_dropped: int
    file_sentences: int


class ReloadErrPayload(TypedDict):
    status: Literal["error"]
    message: str


ReloadPayload = ReloadOkPayload | ReloadErrPayload


def _find_divergence_index(
    prefix: list[rdm_api.PrefixItem],
    file_sentences: list[rdm_api.Sentence],
) -> tuple[int, int]:
    """Return ``(prefix_divergence_idx, file_sentences_consumed)``.

    Walks the document prefix against the parsed file sentences, treating
    ghost items as preserved-but-not-in-file (they contribute no file bytes
    and have no corresponding file sentence). Returns the first prefix index
    where the two disagree, along with the number of file sentences matched
    up to (but not including) that point. If the whole prefix matches, the
    divergence index is ``len(prefix)``.
    """
    file_idx = 0
    for i, item in enumerate(prefix):
        if item.kind == "ghost":
            continue
        if file_idx >= len(file_sentences):
            return i, file_idx
        sent = file_sentences[file_idx]
        if item.kind == sent.kind and item.text == sent.text:
            file_idx += 1
            continue
        return i, file_idx
    return len(prefix), file_idx


async def _parse_file_via_clone(
    cursor: RocqCursor, file_text: str
) -> list[rdm_api.Sentence] | ReloadErrPayload:
    """Parse ``file_text`` on a materialized clone reverted to the start.

    Returns the parsed sentences on success, or a reload-error payload.
    The clone is always disposed before returning.
    """
    clone = await cursor.clone(materialize=True)
    try:
        go = await clone.go_to(0)
        if isinstance(go, rdm_api.Err):
            return {
                "status": "error",
                "message": f"Could not rewind clone cursor to 0: {go.message}",
            }
        parsed = await clone.replace_suffix(file_text)
        if isinstance(parsed, rdm_api.Err):
            return {
                "status": "error",
                "message": f"Sentence split failed: {parsed.message}",
            }
        return parsed
    finally:
        try:
            await clone.dispose()
        except Exception as exc:
            logger.warning("Failed to dispose reload clone cursor: %s", exc)


def _invalidate_cache(cache: FeedbackCache, new_extent: int) -> tuple[int, int]:
    """Trim ``cache.commands`` to entries fully within the new processed extent.

    Returns ``(kept_count, dropped_count)``. Also clears the sticky terminal
    state so the cache can make forward progress on the new document.
    """
    kept: list[CachedCommand] = [
        cmd for cmd in cache.commands if cmd.byte_end <= new_extent
    ]
    dropped = len(cache.commands) - len(kept)
    cache.commands = kept
    cache.processed_extent = new_extent
    cache.terminal = None
    return len(kept), dropped


async def reload_file(
    cursor: RocqCursor,
    cache: FeedbackCache,
    session_lock: asyncio.Lock,
    file_path: Path,
) -> ReloadPayload:
    """Reconcile the live document with the on-disk contents of ``file_path``."""
    async with session_lock:
        try:
            file_text = file_path.read_text(encoding="utf-8")
        except FileNotFoundError:
            return {"status": "error", "message": f"File not found: {file_path}"}
        except OSError as exc:
            return {"status": "error", "message": f"Cannot read {file_path}: {exc}"}
        except UnicodeDecodeError as exc:
            return {"status": "error", "message": f"File is not valid UTF-8: {exc}"}

        parsed = await _parse_file_via_clone(cursor, file_text)
        if isinstance(parsed, dict):
            return parsed

        prefix = await cursor.doc_prefix()
        divergence_idx, file_idx = _find_divergence_index(prefix, parsed)
        reverted_count = len(prefix) - divergence_idx

        if divergence_idx < len(prefix):
            revert_result = await cursor.revert_before(erase=True, index=divergence_idx)
            if isinstance(revert_result, rdm_api.Err):
                return {
                    "status": "error",
                    "message": f"Could not revert cursor to {divergence_idx}: "
                    f"{revert_result.message}",
                }

        remaining_text = "".join(sent.text for sent in parsed[file_idx:])
        replace_result = await cursor.replace_suffix(remaining_text)
        if isinstance(replace_result, rdm_api.Err):
            return {
                "status": "error",
                "message": f"Failed to install new suffix: {replace_result.message}",
            }

        new_prefix = await cursor.doc_prefix()
        new_extent = processed_byte_length(new_prefix)
        kept_count, dropped_count = _invalidate_cache(cache, new_extent)

        return {
            "status": "ok",
            "prefix_items_preserved": divergence_idx,
            "prefix_items_reverted": reverted_count,
            "cached_commands_kept": kept_count,
            "cached_commands_dropped": dropped_count,
            "file_sentences": len(parsed),
        }
