from __future__ import annotations

import logging
from typing import Any, override

from rocq_doc_manager.rocq_cursor_protocol import RocqCursor

from . import rocq_doc_manager_api as rdm_api
from .decorators import ensure_endswith_period
from .rocq_doc_manager_api import RocqDocManagerAPIAsync as AsyncAPI

logger = logging.getLogger(__name__)


class RDMRocqCursor(RocqCursor):
    """
    A RocqCursor backed by a a RocqDocManager.
    """

    def __init__(self, rdm: AsyncAPI, cursor: int) -> None:
        self._the_rdm: AsyncAPI | None = rdm
        self._cursor = cursor

    _NO_CURSOR_ERROR: str = "Unknown cursor"

    @property
    def _rdm(self) -> AsyncAPI:
        if self._the_rdm is None:
            raise Exception(f"Using disposed cursor: {self._cursor}")
        return self._the_rdm

    @override
    async def advance_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        """Advance the cursor before the indicated unprocessed item."""
        return await self._rdm.advance_to(self._cursor, index)

    @override
    async def clear_suffix(self, count: int | None = None) -> None:
        return await self._rdm.clear_suffix(self._cursor, count)

    @override
    async def materialize(self) -> None:
        """Enable parallel processing on this cursor."""
        result = await self._rdm.materialize(self._cursor)
        if result is None:
            return None
        assert isinstance(result, rdm_api.Err)
        raise Exception(result.message)

    @override
    async def clone(self, *, materialize: bool = False) -> RocqCursor:
        result = RDMRocqCursor(self._rdm, await self._rdm.clone(self._cursor))
        if materialize:
            await result.materialize()
        return result

    async def copy_contents(self, dest: RDMRocqCursor) -> None:
        assert self._rdm == dest._rdm  # can not copy across backends
        await self._rdm.copy_contents(src=self._cursor, dst=dest._cursor)

    @override
    async def commit(
        self,
        file: str | None,
        *,
        include_ghost: bool = False,
        include_suffix: bool = True,
    ) -> None | rdm_api.Err[None]:
        return await self._rdm.commit(
            self._cursor,
            file,
            include_ghost=include_ghost,
            include_suffix=include_suffix,
        )

    @override
    async def compile(self) -> rdm_api.CompileResult:
        return await self._rdm.compile(self._cursor)

    @override
    async def cursor_index(self) -> int:
        return await self._rdm.cursor_index(self._cursor)

    @override
    async def dispose(self) -> None:
        await self._rdm.dispose(self._cursor)
        self._the_rdm = None

    @override
    async def doc_prefix(self) -> list[rdm_api.PrefixItem]:
        return await self._rdm.doc_prefix(self._cursor)

    @override
    async def doc_suffix(self) -> list[rdm_api.SuffixItem]:
        return await self._rdm.doc_suffix(self._cursor)

    @override
    async def go_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        return await self._rdm.go_to(self._cursor, index)

    @override
    async def has_suffix(self) -> bool:
        return await self._rdm.has_suffix(self._cursor)

    @override
    async def insert_blanks(self, text: str) -> None:
        return await self._rdm.insert_blanks(self._cursor, text)

    @ensure_endswith_period(argnames="text")
    async def _insert_command(
        self, text: str
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return await self._rdm.insert_command(self._cursor, text)

    @override
    async def load_file(self) -> None | rdm_api.Err[rdm_api.RocqLoc | None]:
        return await self._rdm.load_file(self._cursor)

    # TODO: we should really reduce the repetition on [query],
    # there are 5 functions, but they all do basically the same thing
    @override
    @ensure_endswith_period(argnames="text")
    async def query(self, text: str) -> rdm_api.CommandData | rdm_api.Err[None]:
        return await self._rdm.query(self._cursor, text)

    @override
    @ensure_endswith_period(argnames="text")
    async def query_json(
        self, text: str, *, index: int
    ) -> Any | rdm_api.Err[rdm_api.CommandError]:
        return await self._rdm.query_json(self._cursor, text, index=index)

    @override
    @ensure_endswith_period(argnames="text")
    async def query_json_all(
        self, text: str, *, indices: list[int] | None = None
    ) -> list[Any] | rdm_api.Err[None]:
        return await self._rdm.query_json_all(self._cursor, text, indices=indices)

    @override
    @ensure_endswith_period(argnames="text")
    async def query_text(self, text: str, *, index: int) -> str | rdm_api.Err[None]:
        return await self._rdm.query_text(self._cursor, text, index=index)

    @override
    @ensure_endswith_period(argnames="text")
    async def query_text_all(
        self, text: str, *, indices: list[int] | None = None
    ) -> list[str] | rdm_api.Err[None]:
        return await self._rdm.query_text_all(self._cursor, text, indices=indices)

    @override
    async def revert_before(self, erase: bool, index: int) -> None:
        return await self._rdm.revert_before(self._cursor, erase, index)

    @override
    @ensure_endswith_period(argnames="text")
    async def run_command(self, text: str) -> rdm_api.CommandData | rdm_api.Err[None]:
        return await self._rdm.run_command(self._cursor, text)

    @override
    async def run_step(
        self,
    ) -> rdm_api.CommandData | None | rdm_api.Err[rdm_api.CommandError]:
        return await self._rdm.run_step(self._cursor)

    # @override
    # async def run_steps(self, count: int) -> None | rdm_api.Err[rdm_api.StepsError]:
    #     return await self._rdm.run_steps(self._cursor, count)
