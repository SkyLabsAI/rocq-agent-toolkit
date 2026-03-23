from __future__ import annotations

import logging
from typing import override

from .. import rocq_doc_manager_api as rdm_api
from .delegate import DelegateRocqCursor
from .protocol import RocqCursor

logger = logging.getLogger(__name__)


class DelimitedRocqCursor(DelegateRocqCursor):
    """
    A RocqCursor that only has access to a portion of a Rocq document.
    """

    def __init__(
        self,
        cursor: RocqCursor,
        excl_prefix_items: int,
        excl_suffix_items: int,
    ) -> None:
        self._cursor = cursor
        self._excl_prefix_items = excl_prefix_items
        self._excl_suffix_items = excl_suffix_items

    @classmethod
    async def make(
        cls,
        cursor: RocqCursor,
        *,
        start: int | None = None,
        end: int | None = None,
        count: int | None = None,
        materialize: bool = False,
    ) -> DelimitedRocqCursor | rdm_api.Err[rdm_api.CommandError | None]:
        """
        Creates a delimited cursor from (a clone of) the given cursor. If the
        creation is successful, the returned cursor points to the start of the
        region. A command error (as returned by `go_to`) is returned if the
        document cannot be processed to the start of the newly created cursor.

        @param cursor: the underlying cursor (it is cloned)
        @param start: index of the first document item in the region (defaults
            to the current index of `cursor` if not given)
        @param end: index of the fist document item after the region (defaults
            to the final index of the document, incompatible with `count`)
        @param count: number of items to include in the region (incompatible
            with `end`, has no effect if not set)
        @param materialize: materializes the cloned cursor if set to `True`
        @returns: the delimited cursor or a command error
        @raises ValueError: if the `start` and `end` values are not suitable
        """
        prefix_len = await cursor.cursor_index()
        suffix_len = len(await cursor.doc_suffix())
        total_len = prefix_len + suffix_len
        start_index = prefix_len if start is None else start
        if end and count:
            raise ValueError('Arguments "end" and "count" should not be both set')
        end_index = total_len if end is None else end
        end_index = end_index if count is None else start_index + count
        # Check that the indices make sense.
        if not (0 <= start_index <= total_len):
            raise ValueError(
                f'Argument "start" ({start_index}) not between 0 and {total_len}'
            )
        if not (0 <= end_index <= total_len):
            raise ValueError(
                f'Argument "end" ({end_index}) not between 0 and {total_len}'
            )
        if not (start_index <= end_index):
            raise ValueError(
                f'Argument "start" ({start_index}) should be smaller "end" ({end_index})'
            )
        # Clone the cursor, move to the start of the region, dispose on error
        cursor = await cursor.clone(materialize=materialize)
        if start is not None:
            res = await cursor.go_to(start_index)
            if isinstance(res, rdm_api.Err):
                await cursor.dispose()
                return res
        # Create the delimited cursor
        return cls(cursor, start_index, total_len - end_index)

    async def _translate_index(self, index: int) -> int:
        if index < 0:
            raise Exception(f"Invalid (negative) index {index}")
        total_len = len(await self.doc_prefix()) + len(await self.doc_suffix())
        if total_len < index:
            raise Exception(f"Invalid index {index} (should not exceed {total_len})")
        return index + self._excl_prefix_items

    @override
    async def advance_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        index = await self._translate_index(index)
        return await self._cursor.advance_to(index)

    @override
    async def clear_suffix(self, count: int | None = None) -> None:
        suffix = await self.doc_suffix()
        len_suffix = len(suffix)
        nb_to_clear = len_suffix if count is None else count
        if len_suffix < nb_to_clear:
            raise Exception(
                f"Cannot clear {nb_to_clear} suffix items (limited to {len_suffix})"
            )
        await self._cursor.clear_suffix(nb_to_clear)

    @override
    async def clone(self, *, materialize: bool = False) -> RocqCursor:
        cursor = await self._cursor.clone()
        return DelimitedRocqCursor(
            cursor, self._excl_prefix_items, self._excl_suffix_items
        )

    @override
    async def commit(
        self,
        file: str | None,
        *,
        include_ghost: bool = False,
        include_suffix: bool = True,
    ) -> None | rdm_api.Err[None]:
        raise Exception("Cannot commit using a delimited cursor")

    @override
    async def cursor_index(self) -> int:
        index = await self._cursor.cursor_index()
        assert self._excl_prefix_items <= index
        return index - self._excl_prefix_items

    @override
    async def doc_prefix(self) -> list[rdm_api.PrefixItem]:
        prefix = await self._cursor.doc_prefix()
        assert len(prefix) >= self._excl_prefix_items
        return prefix[self._excl_prefix_items :]

    @override
    async def doc_suffix(self) -> list[rdm_api.SuffixItem]:
        suffix = await self._cursor.doc_suffix()
        len_suffix = len(suffix)
        assert len_suffix >= self._excl_suffix_items
        return suffix[: len_suffix - self._excl_suffix_items]

    @override
    async def go_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        index = await self._translate_index(index)
        return await self._cursor.go_to(index)

    @override
    async def has_suffix(self) -> bool:
        suffix = await self._cursor.doc_suffix()
        return len(suffix) != self._excl_suffix_items

    @override
    async def load_file(self) -> None | rdm_api.Err[rdm_api.RocqLoc | None]:
        raise Exception("Cannot load file using a delimited cursor")

    @override
    async def revert_before(self, erase: bool, index: int) -> None:
        index = await self._translate_index(index)
        await self._cursor.revert_before(erase, index)

    @override
    async def run_step(
        self,
    ) -> rdm_api.CommandData | None | rdm_api.Err[rdm_api.CommandError]:
        if not await self.has_suffix():
            raise Exception("No item left to process")
        return await self._cursor.run_step()
