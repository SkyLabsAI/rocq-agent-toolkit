from __future__ import annotations

import logging
from typing import Any, override

from rocq_doc_manager.rocq_cursor_protocol import RocqCursor

from . import rocq_doc_manager_api as rdm_api
from .decorators import ensure_endswith_period
from .rocq_doc_manager_api import RocqDocManagerAPI as API

logger = logging.getLogger(__name__)


class RDMRocqCursor(RocqCursor):
    """
    A RocqCursor backed by a a RocqDocManager.
    """

    def __init__(self, rdm: API, cursor: int) -> None:
        self._the_rdm: API | None = rdm
        self._cursor = cursor

    _NO_CURSOR_ERROR: str = "Unknown cursor"

    @property
    def _rdm(self) -> API:
        if self._the_rdm is None:
            raise Exception(f"Using disposed cursor: {self._cursor}")
        return self._the_rdm

    @override
    def advance_to(self, index: int) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        """Advance the cursor before the indicated unprocessed item."""
        return self._rdm.advance_to(self._cursor, index)

    @override
    def clear_suffix(self, count: int | None = None) -> None:
        return self._rdm.clear_suffix(self._cursor, count)

    @override
    def materialize(self) -> None:
        """Enable parallel processing on this cursor."""
        result = self._rdm.materialize(self._cursor)
        if result is None:
            return None
        assert isinstance(result, rdm_api.Err)
        raise Exception(result.message)

    @override
    def clone(self, *, materialize: bool = False) -> RocqCursor:
        result = RDMRocqCursor(self._rdm, self._rdm.clone(self._cursor))
        if materialize:
            result.materialize()
        return result

    def copy_contents(self, dest: RDMRocqCursor) -> None:
        assert self._rdm == dest._rdm  # can not copy across backends
        self._rdm.copy_contents(src=self._cursor, dst=dest._cursor)

    @override
    def commit(
        self,
        file: str | None,
        *,
        include_ghost: bool = False,
        include_suffix: bool = True,
    ) -> None | rdm_api.Err[None]:
        return self._rdm.commit(
            self._cursor,
            file,
            include_ghost=include_ghost,
            include_suffix=include_suffix,
        )

    @override
    def compile(self) -> rdm_api.CompileResult:
        return self._rdm.compile(self._cursor)

    @override
    def cursor_index(self) -> int:
        return self._rdm.cursor_index(self._cursor)

    @override
    def dispose(self) -> None:
        self._rdm.dispose(self._cursor)
        self._the_rdm = None

    @override
    def doc_prefix(self) -> list[rdm_api.PrefixItem]:
        return self._rdm.doc_prefix(self._cursor)

    @override
    def doc_suffix(self) -> list[rdm_api.SuffixItem]:
        return self._rdm.doc_suffix(self._cursor)

    @override
    def go_to(self, index: int) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        return self._rdm.go_to(self._cursor, index)

    @override
    def has_suffix(self) -> bool:
        return self._rdm.has_suffix(self._cursor)

    @override
    def insert_blanks(self, text: str) -> None:
        return self._rdm.insert_blanks(self._cursor, text)

    @ensure_endswith_period(argnames="text")
    def _insert_command(
        self, text: str
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return self._rdm.insert_command(self._cursor, text)

    @override
    def load_file(self) -> None | rdm_api.Err[rdm_api.RocqLoc | None]:
        return self._rdm.load_file(self._cursor)

    # TODO: we should really reduce the repetition on [query],
    # there are 5 functions, but they all do basically the same thing
    @override
    @ensure_endswith_period(argnames="text")
    def query(self, text: str) -> rdm_api.CommandData | rdm_api.Err[None]:
        return self._rdm.query(self._cursor, text)

    @override
    @ensure_endswith_period(argnames="text")
    def query_json(
        self, text: str, *, index: int
    ) -> Any | rdm_api.Err[rdm_api.CommandError]:
        return self._rdm.query_json(self._cursor, text, index=index)

    @override
    @ensure_endswith_period(argnames="text")
    def query_json_all(
        self, text: str, *, indices: list[int] | None = None
    ) -> list[Any] | rdm_api.Err[None]:
        return self._rdm.query_json_all(self._cursor, text, indices=indices)

    @override
    @ensure_endswith_period(argnames="text")
    def query_text(self, text: str, *, index: int) -> str | rdm_api.Err[None]:
        return self._rdm.query_text(self._cursor, text, index=index)

    @override
    @ensure_endswith_period(argnames="text")
    def query_text_all(
        self, text: str, *, indices: list[int] | None = None
    ) -> list[str] | rdm_api.Err[None]:
        return self._rdm.query_text_all(self._cursor, text, indices=indices)

    @override
    def revert_before(self, erase: bool, index: int) -> None:
        return self._rdm.revert_before(self._cursor, erase, index)

    @override
    @ensure_endswith_period(argnames="text")
    def run_command(self, text: str) -> rdm_api.CommandData | rdm_api.Err[None]:
        return self._rdm.run_command(self._cursor, text)

    @override
    def run_step(
        self,
    ) -> rdm_api.CommandData | None | rdm_api.Err[rdm_api.CommandError]:
        return self._rdm.run_step(self._cursor)

    @override
    def run_steps(self, count: int) -> None | rdm_api.Err[rdm_api.StepsError]:
        return self._rdm.run_steps(self._cursor, count)
