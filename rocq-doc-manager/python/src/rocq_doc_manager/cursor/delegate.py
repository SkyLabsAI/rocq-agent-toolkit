from typing import Any, override

from .. import rocq_doc_manager_api as rdm_api
from .protocol import RocqCursor


class DelegateRocqCursor(RocqCursor):
    """A RocqCursor that passes through all functionality to an underlying cursor.

    Builders of cursors can use this build new wrappers around RocqCursor and selectively
    override only specific fields.

    The underlying cursor is available as `self._cursor` which should be treated as `protected`,
    i.e. subclasses may access the field but users should not.

    The `make_derived` method should be overridden to build the appropriate cursor.
    """

    def __init__(self, rc: RocqCursor) -> None:
        self._cursor = rc

    def make_derived(self, rc: RocqCursor) -> RocqCursor:
        """Make a value of this cursor type"""
        return self.__class__(rc)

    @override
    async def clone(self, *, materialize: bool = False) -> RocqCursor:
        return self.make_derived(await self._cursor.clone(materialize=materialize))

    @override
    async def _insert_command(
        self, text: str, *, ghost: bool = False
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return await self._cursor._insert_command(text, ghost=ghost)

    @override
    async def run_step(
        self,
    ) -> rdm_api.CommandData | None | rdm_api.Err[rdm_api.CommandError]:
        return await self._cursor.run_step()

    @override
    async def run_steps(self, count: int) -> None | rdm_api.Err[rdm_api.StepsError]:
        return await self._cursor.run_steps(count)

    @override
    async def query(self, text: str) -> rdm_api.CommandData | rdm_api.Err[None]:
        return await self._cursor.query(text)

    @override
    async def query_json(
        self, text: str, *, index: int
    ) -> Any | rdm_api.Err[rdm_api.CommandError]:
        return await self._cursor.query_json(text, index=index)

    @override
    async def query_json_all(
        self, text: str, *, indices: list[int] | None = None
    ) -> list[Any] | rdm_api.Err[None]:
        return await self._cursor.query_json_all(text, indices=indices)

    @override
    async def query_text(self, text: str, *, index: int) -> str | rdm_api.Err[None]:
        return await self._cursor.query_text(text, index=index)

    @override
    async def query_text_all(
        self, text: str, *, indices: list[int] | None = None
    ) -> list[str] | rdm_api.Err[None]:
        return await self._cursor.query_text_all(text, indices=indices)

    @override
    async def revert_before(self, erase: bool, index: int) -> None | rdm_api.Err[None]:
        return await self._cursor.revert_before(erase, index)

    @override
    async def advance_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        # TODO: it might be necessary to insert all of the commands here
        return await self._cursor.advance_to(index=index)

    @override
    async def go_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        return await self._cursor.go_to(index)

    @override
    async def doc_prefix(self) -> list[rdm_api.PrefixItem]:
        return await self._cursor.doc_prefix()

    @override
    async def doc_suffix(self) -> list[rdm_api.SuffixItem]:
        return await self._cursor.doc_suffix()

    @override
    async def clear_suffix(self, count: int | None = None) -> None:
        return await self._cursor.clear_suffix(count)

    @override
    async def commit(
        self,
        file: str | None,
        *,
        include_ghost: bool = False,
        include_suffix: bool = True,
    ) -> None | rdm_api.Err[None]:
        return await self._cursor.commit(
            file, include_ghost=include_ghost, include_suffix=include_suffix
        )

    @override
    async def materialize(self) -> None:
        return await self._cursor.materialize()

    @override
    async def cursor_index(self) -> int:
        return await self._cursor.cursor_index()

    @override
    async def dispose(self) -> None:
        return await self._cursor.dispose()

    @override
    async def has_suffix(self) -> bool:
        return await self._cursor.has_suffix()

    @override
    async def insert_blanks(self, text: str) -> None:
        return await self._cursor.insert_blanks(text)

    @override
    async def load_file(self) -> None | rdm_api.Err[rdm_api.RocqLoc | None]:
        return await self._cursor.load_file()

    @override
    async def split_sentences(
        self, text: str
    ) -> list[rdm_api.Sentence] | rdm_api.Err[rdm_api.SentenceSplitError]:
        return await self._cursor.split_sentences(text)
