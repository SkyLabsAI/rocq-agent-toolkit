from __future__ import annotations

import logging
from typing import Any, override

from rocq_doc_manager.cursor_mixin import CursorMixin

from .rocq_doc_manager_api import RocqDocManagerAPI

logger = logging.getLogger(__name__)


class RocqCursor(CursorMixin):
    """
    Cursors represent a pointer into a Rocq document.
    """

    def __init__(self, rdm: RocqDocManagerAPI, cursor: int) -> None:
        self._the_rdm: RocqDocManagerAPI | None = rdm
        self._cursor = cursor

    _NO_CURSOR_ERROR: str = "Unknown cursor"

    def _check_cursor[T, U](
        self, result: T | RocqDocManagerAPI.Err[None | U]
    ) -> T | RocqDocManagerAPI.Err[U]:
        if isinstance(result, RocqDocManagerAPI.Err):
            if result.message == RocqCursor._NO_CURSOR_ERROR:
                raise Exception(f"Unknown cursor {self._cursor}")
        return result  # type: ignore

    def _check_cursor_keep[T, U](
        self, result: T | RocqDocManagerAPI.Err[None | U]
    ) -> T | RocqDocManagerAPI.Err[None | U]:
        if isinstance(result, RocqDocManagerAPI.Err):
            if result.message == RocqCursor._NO_CURSOR_ERROR:
                raise Exception(f"Unknown cursor {self._cursor}")
        return result

    def _take_cursor[T](self, result: T | RocqDocManagerAPI.Err[None]) -> T:
        if isinstance(result, RocqDocManagerAPI.Err):
            assert result.message == RocqCursor._NO_CURSOR_ERROR
            raise Exception(f"Unknown cursor: {self._cursor}")
        return result

    @property
    def _rdm(self) -> RocqDocManagerAPI:
        if self._the_rdm is None:
            raise Exception(f"Using disposed cursor: {self._cursor}")
        return self._the_rdm

    @override
    def advance_to(
        self, index: int
    ) -> None | RocqDocManagerAPI.Err[RocqDocManagerAPI.CommandError | None]:
        """Advance the cursor before the indicated unprocessed item."""
        return self._check_cursor(self._rdm.advance_to(self._cursor, index))

    @override
    def clear_suffix(self) -> None:
        return self._take_cursor(self._rdm.clear_suffix(self._cursor))

    @override
    def materialize(self) -> None:
        """Enable parallel processing on this cursor."""
        pass

    @override
    def clone(self, materialize: bool = False) -> RocqCursor:
        result = RocqCursor(self._rdm, self._take_cursor(self._rdm.clone(self._cursor)))
        if materialize:
            result.materialize()
        return result

    @override
    def commit(self, include_suffix: bool) -> None:
        return self._take_cursor(self._rdm.commit(self._cursor, include_suffix))

    @override
    def compile(self) -> RocqDocManagerAPI.CompileResult:
        return self._take_cursor(self._rdm.compile(self._cursor))

    @override
    def cursor_index(self) -> int:
        return self._take_cursor(self._rdm.cursor_index(self._cursor))

    @override
    def dispose(self) -> None:
        self._take_cursor(self._rdm.dispose(self._cursor))
        self._the_rdm = None

    @override
    def doc_prefix(self) -> list[RocqDocManagerAPI.PrefixItem]:
        return self._take_cursor(self._rdm.doc_prefix(self._cursor))

    @override
    def doc_suffix(self) -> list[RocqDocManagerAPI.SuffixItem]:
        return self._take_cursor(self._rdm.doc_suffix(self._cursor))

    @override
    def go_to(
        self, index: int
    ) -> None | RocqDocManagerAPI.Err[RocqDocManagerAPI.CommandError]:
        return self._check_cursor(self._rdm.go_to(self._cursor, index))

    @override
    def has_suffix(self) -> bool:
        return self._take_cursor(self._rdm.has_suffix(self._cursor))

    @override
    def insert_blanks(self, text: str) -> None:
        return self._take_cursor(self._rdm.insert_blanks(self._cursor, text))

    @override
    def insert_command(
        self, text: str, blanks: str | None = "\n"
    ) -> (
        RocqDocManagerAPI.CommandData
        | RocqDocManagerAPI.Err[RocqDocManagerAPI.CommandError]
    ):
        return self._check_cursor(self._rdm.insert_command(self._cursor, text))

    @override
    def load_file(self) -> None | RocqDocManagerAPI.Err[RocqDocManagerAPI.RocqLoc]:
        return self._check_cursor(self._rdm.load_file(self._cursor))

    # TODO: we should really reduce the repetition on [query],
    # there are 5 functions, but they all do basically the same thing
    @override
    def query(
        self, text: str
    ) -> (
        RocqDocManagerAPI.CommandData
        | RocqDocManagerAPI.Err[RocqDocManagerAPI.CommandError]
    ):
        return self._check_cursor(self._rdm.query(self._cursor, text))

    @override
    def query_json(
        self, text: str, index: int
    ) -> Any | RocqDocManagerAPI.Err[RocqDocManagerAPI.CommandError]:
        return self._check_cursor(self._rdm.query_json(self._cursor, text, index))

    @override
    def query_json_all(
        self, text: str, indices: list[int] | None = None
    ) -> list[Any] | RocqDocManagerAPI.Err[RocqDocManagerAPI.CommandError]:
        return self._check_cursor(self._rdm.query_json_all(self._cursor, text, indices))

    @override
    def query_text(
        self, text: str, index: int
    ) -> str | RocqDocManagerAPI.Err[RocqDocManagerAPI.CommandError]:
        return self._check_cursor(self._rdm.query_text(self._cursor, text, index))

    @override
    def query_text_all(
        self, text: str, indices: list[int] | None = None
    ) -> list[str] | RocqDocManagerAPI.Err[RocqDocManagerAPI.CommandError]:
        return self._check_cursor(self._rdm.query_text_all(self._cursor, text, indices))

    @override
    def revert_before(
        self, erase: bool, index: int
    ) -> None | RocqDocManagerAPI.Err[None]:
        return self._check_cursor(self._rdm.revert_before(self._cursor, erase, index))

    @override
    def run_command(
        self, text: str
    ) -> (
        RocqDocManagerAPI.CommandData
        | RocqDocManagerAPI.Err[RocqDocManagerAPI.CommandError]
    ):
        return self._check_cursor(self._rdm.run_command(self._cursor, text))

    @override
    def run_step(
        self,
    ) -> (
        RocqDocManagerAPI.CommandData
        | None
        | RocqDocManagerAPI.Err[RocqDocManagerAPI.CommandError]
    ):
        return self._check_cursor(self._rdm.run_step(self._cursor))
