from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Any, TypeAlias

from jsonrpc_tp import JsonRPCTP

from .rocq_doc_manager_api import RocqDocManagerAPI


class RocqCursorProtocol(ABC):
    """
    Cursors represent a pointer into a Rocq document.
    """

    Err: TypeAlias = JsonRPCTP.Err  # noqa: UP040
    Resp: TypeAlias = JsonRPCTP.Resp  # noqa: UP040
    Error: TypeAlias = JsonRPCTP.Error  # noqa: UP040
    RocqSource: TypeAlias = RocqDocManagerAPI.RocqSource  # noqa: UP040
    RocqLoc: TypeAlias = RocqDocManagerAPI.RocqLoc  # noqa: UP040
    Quickfix: TypeAlias = RocqDocManagerAPI.Quickfix  # noqa: UP040
    FeedbackMessage: TypeAlias = RocqDocManagerAPI.FeedbackMessage  # noqa: UP040
    GlobrefsDiff: TypeAlias = RocqDocManagerAPI.GlobrefsDiff  # noqa: UP040
    ProofState: TypeAlias = RocqDocManagerAPI.ProofState  # noqa: UP040
    CommandData: TypeAlias = RocqDocManagerAPI.CommandData  # noqa: UP040
    CommandError: TypeAlias = RocqDocManagerAPI.CommandError  # noqa: UP040
    PrefixItem: TypeAlias = RocqDocManagerAPI.PrefixItem  # noqa: UP040
    SuffixItem: TypeAlias = RocqDocManagerAPI.SuffixItem  # noqa: UP040
    CompileResult: TypeAlias = RocqDocManagerAPI.CompileResult  # noqa: UP040

    @abstractmethod
    def advance_to(
        self, index: int
    ) -> None | RocqDocManagerAPI.Err[RocqDocManagerAPI.CommandError | None]: ...

    @abstractmethod
    def clear_suffix(self) -> None: ...

    @abstractmethod
    def materialize(self) -> None:
        """Enable parallel processing on this cursor."""
        ...

    @abstractmethod
    def clone(self, materialize: bool = False) -> RocqCursorProtocol: ...

    @abstractmethod
    def copy_into(self, dest: RocqCursorProtocol) -> None: ...

    @abstractmethod
    def commit(self, file: str | None, include_suffix: bool) -> None: ...

    @abstractmethod
    def compile(self) -> RocqDocManagerAPI.CompileResult: ...

    @abstractmethod
    def cursor_index(self) -> int: ...

    @abstractmethod
    def dispose(self) -> None: ...

    @abstractmethod
    def doc_prefix(self) -> list[RocqDocManagerAPI.PrefixItem]: ...

    @abstractmethod
    def doc_suffix(self) -> list[RocqDocManagerAPI.SuffixItem]: ...

    @abstractmethod
    def go_to(
        self, index: int
    ) -> None | RocqDocManagerAPI.Err[RocqDocManagerAPI.CommandError | None]: ...

    @abstractmethod
    def has_suffix(self) -> bool: ...

    @abstractmethod
    def insert_blanks(self, text: str) -> None: ...

    @abstractmethod
    def insert_command(
        self, text: str
    ) -> (
        RocqDocManagerAPI.CommandData
        | RocqDocManagerAPI.Err[RocqDocManagerAPI.CommandError]
    ): ...

    @abstractmethod
    def load_file(
        self,
    ) -> None | RocqDocManagerAPI.Err[RocqDocManagerAPI.RocqLoc | None]: ...

    # TODO: we should really reduce the repetition on [query],
    # there are 5 functions, but they all do basically the same thing
    @abstractmethod
    def query(
        self, text: str
    ) -> RocqDocManagerAPI.CommandData | RocqDocManagerAPI.Err[None]: ...

    @abstractmethod
    def query_json(
        self, text: str, index: int
    ) -> Any | RocqDocManagerAPI.Err[None]: ...

    @abstractmethod
    def query_json_all(
        self, text: str, indices: list[int] | None
    ) -> list[Any] | RocqDocManagerAPI.Err[None]: ...

    @abstractmethod
    def query_text(
        self, text: str, index: int
    ) -> str | RocqDocManagerAPI.Err[None]: ...

    @abstractmethod
    def query_text_all(
        self, text: str, indices: list[int] | None
    ) -> list[str] | RocqDocManagerAPI.Err[None]: ...

    @abstractmethod
    def revert_before(
        self, erase: bool, index: int
    ) -> None | RocqDocManagerAPI.Err[None]: ...

    @abstractmethod
    def run_command(
        self, text: str
    ) -> RocqDocManagerAPI.CommandData | RocqDocManagerAPI.Err[None]: ...

    @abstractmethod
    def run_step(
        self,
    ) -> (
        RocqDocManagerAPI.CommandData
        | None
        | RocqDocManagerAPI.Err[RocqDocManagerAPI.CommandError | None]
    ): ...
