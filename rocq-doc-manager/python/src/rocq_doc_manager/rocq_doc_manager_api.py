from __future__ import annotations

from dataclasses import dataclass, field

# ruff: noqa: C416 -- unnecessary list comprehension
from typing import Any, Literal

from dataclasses_json import DataClassJsonMixin
from jsonrpc_tp import Err, Error, JsonRPCTP, Resp

__all__ = [
    "RocqDocManagerAPI",
    "Err",
    "Error",
    "Resp",
    "CompileResult",
    "SuffixItem",
    "PrefixItem",
    "CommandError",
    "CommandData",
    "ProofState",
    "GlobrefsDiff",
    "FeedbackMessage",
    "Quickfix",
    "RocqLoc",
    "RocqSource",
]


@dataclass(frozen=True)
class RocqSource(DataClassJsonMixin):
    """Rocq source file information."""

    file: str = field(kw_only=True, default="")
    dirpath: str | None = field(kw_only=True, default=None)


@dataclass(frozen=True)
class RocqLoc(DataClassJsonMixin):
    """Rocq source code location."""

    # End position.
    ep: int = field(kw_only=True, default=0)
    # Start position.
    bp: int = field(kw_only=True, default=0)
    # Position of the beginning of end line.
    bol_pos_last: int = field(kw_only=True, default=0)
    # End line number.
    line_nb_last: int = field(kw_only=True, default=0)
    # Position of the beginning of start line.
    bol_pos: int = field(kw_only=True, default=0)
    # Start line number.
    line_nb: int = field(kw_only=True, default=0)
    # Source file identification if not run as a toplevel.
    fname: RocqSource | None = field(kw_only=True, default=None)


@dataclass(frozen=True)
class Quickfix(DataClassJsonMixin):
    """Quick fix hint."""

    text: str = field(kw_only=True, default="")
    loc: RocqLoc = field(kw_only=True, default_factory=lambda: RocqLoc())


@dataclass(frozen=True)
class FeedbackMessage(DataClassJsonMixin):
    """Rocq feedback message."""

    text: str = field(kw_only=True, default="")
    quickfix: list[Quickfix] = field(kw_only=True, default_factory=list)
    loc: RocqLoc | None = field(kw_only=True, default=None)
    level: Literal["debug", "info", "notice", "warning", "error"] = field(
        kw_only=True, default="notice"
    )


@dataclass(frozen=True)
class GlobrefsDiff(DataClassJsonMixin):
    """Environment modification performed by a Rocq command."""

    removed_inductives: list[str] = field(kw_only=True, default_factory=list)
    added_inductives: list[str] = field(kw_only=True, default_factory=list)
    removed_constants: list[str] = field(kw_only=True, default_factory=list)
    added_constants: list[str] = field(kw_only=True, default_factory=list)


@dataclass(frozen=True)
class ProofState(DataClassJsonMixin):
    """Summary of a Rocq proof state, including the text of focused goals."""

    focused_goals: list[str] = field(kw_only=True, default_factory=list)
    unfocused_goals: list[int] = field(kw_only=True, default_factory=list)
    shelved_goals: int = field(kw_only=True, default=0)
    given_up_goals: int = field(kw_only=True, default=0)


@dataclass(frozen=True)
class CommandData(DataClassJsonMixin):
    """Data gathered while running a Rocq command."""

    proof_state: ProofState | None = field(kw_only=True, default=None)
    feedback_messages: list[FeedbackMessage] = field(kw_only=True, default_factory=list)
    globrefs_diff: GlobrefsDiff = field(
        kw_only=True, default_factory=lambda: GlobrefsDiff()
    )


@dataclass(frozen=True)
class CommandError(DataClassJsonMixin):
    """Data returned on Rocq command errors."""

    feedback_messages: list[FeedbackMessage] = field(kw_only=True, default_factory=list)
    # Optional source code location for the error.
    error_loc: RocqLoc | None = field(kw_only=True, default=None)


@dataclass(frozen=True)
class PrefixItem(DataClassJsonMixin):
    """Document prefix item, appearing before the cursor."""

    text: str = field(kw_only=True, default="")
    offset: int = field(kw_only=True, default=0)
    kind: Literal["blanks", "command", "ghost"] = field(kw_only=True, default="command")


@dataclass(frozen=True)
class SuffixItem(DataClassJsonMixin):
    """Document suffix item, appearing after the cursor."""

    text: str = field(kw_only=True, default="")
    kind: Literal["blanks", "command", "ghost"] = field(kw_only=True, default="command")


@dataclass(frozen=True)
class CompileResult(DataClassJsonMixin):
    """Result of the `compile` method."""

    # Non-null if success is false.
    error: str | None = field(kw_only=True, default=None)
    stderr: str = field(kw_only=True, default="")
    stdout: str = field(kw_only=True, default="")
    success: bool = field(kw_only=True, default=False)


class RocqDocManagerAPI:
    """Main API class."""

    def __init__(self, rpc: JsonRPCTP) -> None:
        self._rpc: JsonRPCTP = rpc

    def advance_to(self, cursor: int, index: int) -> None | Err[CommandError | None]:
        """Advance the cursor before the indicated unprocessed item."""
        result = self._rpc.raw_request("advance_to", [cursor, index])
        if isinstance(result, Err):
            data = None if result.data is None else CommandError.from_dict(result.data)
            return Err(result.message, data)
        return None

    def clear_suffix(self, cursor: int, count: int | None) -> None:
        """Remove unprocessed commands from the document."""
        result = self._rpc.raw_request("clear_suffix", [cursor, count])
        assert not isinstance(result, Err)
        return None

    def clone(self, cursor: int) -> int:
        """Clones the given cursor."""
        result = self._rpc.raw_request("clone", [cursor])
        assert not isinstance(result, Err)
        return int(result.result)

    def commit(
        self, cursor: int, file: str | None, include_ghost: bool, include_suffix: bool
    ) -> None:
        """Write the current document contents to the file."""
        result = self._rpc.raw_request(
            "commit", [cursor, file, include_ghost, include_suffix]
        )
        assert not isinstance(result, Err)
        return None

    def compile(self, cursor: int) -> CompileResult:
        """Compile the current contents of the file with `rocq compile`."""
        result = self._rpc.raw_request("compile", [cursor])
        assert not isinstance(result, Err)
        return CompileResult.from_dict(result.result)

    def contents(self, cursor: int, include_ghost: bool, include_suffix: bool) -> str:
        """Gives the current contents of the document, as if it was written to a file."""
        result = self._rpc.raw_request(
            "contents", [cursor, include_ghost, include_suffix]
        )
        assert not isinstance(result, Err)
        return str(result.result)

    def copy_contents(self, src: int, dst: int) -> None:
        """Copies the contents of src into dst."""
        result = self._rpc.raw_request("copy_contents", [src, dst])
        assert not isinstance(result, Err)
        return None

    def cursor_index(self, cursor: int) -> int:
        """Gives the index at the cursor."""
        result = self._rpc.raw_request("cursor_index", [cursor])
        assert not isinstance(result, Err)
        return int(result.result)

    def dispose(self, cursor: int) -> None:
        """Destroys the cursor."""
        result = self._rpc.raw_request("dispose", [cursor])
        assert not isinstance(result, Err)
        return None

    def doc_prefix(self, cursor: int) -> list[PrefixItem]:
        """Gives the list of all processed commands, appearing before the cursor."""
        result = self._rpc.raw_request("doc_prefix", [cursor])
        assert not isinstance(result, Err)
        return [PrefixItem.from_dict(v1) for v1 in result.result]

    def doc_suffix(self, cursor: int) -> list[SuffixItem]:
        """Gives the list of all unprocessed commands, appearing after the cursor."""
        result = self._rpc.raw_request("doc_suffix", [cursor])
        assert not isinstance(result, Err)
        return [SuffixItem.from_dict(v1) for v1 in result.result]

    def dump(self, cursor: int) -> Any:
        """Dump the document contents (debug)."""
        result = self._rpc.raw_request("dump", [cursor])
        assert not isinstance(result, Err)
        return result.result

    def go_to(self, cursor: int, index: int) -> None | Err[CommandError | None]:
        """Move the cursor right before the indicated item (whether it is already processed or not)."""
        result = self._rpc.raw_request("go_to", [cursor, index])
        if isinstance(result, Err):
            data = None if result.data is None else CommandError.from_dict(result.data)
            return Err(result.message, data)
        return None

    def has_suffix(self, cursor: int) -> bool:
        """Indicates whether the document has a suffix (unprocessed items)."""
        result = self._rpc.raw_request("has_suffix", [cursor])
        assert not isinstance(result, Err)
        return bool(result.result)

    def insert_blanks(self, cursor: int, text: str) -> None:
        """Insert and process blanks at the cursor."""
        result = self._rpc.raw_request("insert_blanks", [cursor, text])
        assert not isinstance(result, Err)
        return None

    def insert_command(self, cursor: int, text: str) -> CommandData | Err[CommandError]:
        """Insert and process a command at the cursor."""
        result = self._rpc.raw_request("insert_command", [cursor, text])
        if isinstance(result, Err):
            data = CommandError.from_dict(result.data)
            return Err(result.message, data)
        return CommandData.from_dict(result.result)

    def load_file(self, cursor: int) -> None | Err[RocqLoc | None]:
        """Adds the (unprocessed) file contents to the document (note that this requires running sentence-splitting, which requires the input file not to have syntax errors)."""
        result = self._rpc.raw_request("load_file", [cursor])
        if isinstance(result, Err):
            data = None if result.data is None else RocqLoc.from_dict(result.data)
            return Err(result.message, data)
        return None

    def materialize(self, cursor: int) -> None | Err[None]:
        """Materializes the cursor, giving it its own dedicated top-level."""
        result = self._rpc.raw_request("materialize", [cursor])
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return None

    def query(self, cursor: int, text: str) -> CommandData | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = self._rpc.raw_request("query", [cursor, text])
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return CommandData.from_dict(result.result)

    def query_json(self, cursor: int, text: str, index: int) -> Any | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = self._rpc.raw_request("query_json", [cursor, text, index])
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return result.result

    def query_json_all(
        self, cursor: int, text: str, indices: list[int] | None
    ) -> list[Any] | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = self._rpc.raw_request("query_json_all", [cursor, text, indices])
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return [v1 for v1 in result.result]

    def query_text(self, cursor: int, text: str, index: int) -> str | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = self._rpc.raw_request("query_text", [cursor, text, index])
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return str(result.result)

    def query_text_all(
        self, cursor: int, text: str, indices: list[int] | None
    ) -> list[str] | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = self._rpc.raw_request("query_text_all", [cursor, text, indices])
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return [str(v1) for v1 in result.result]

    def revert_before(self, cursor: int, erase: bool, index: int) -> None:
        """Revert the cursor to an earlier point in the document."""
        result = self._rpc.raw_request("revert_before", [cursor, erase, index])
        assert not isinstance(result, Err)
        return None

    def run_command(self, cursor: int, text: str) -> CommandData | Err[None]:
        """Process a command at the cursor without inserting it in the document."""
        result = self._rpc.raw_request("run_command", [cursor, text])
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return CommandData.from_dict(result.result)

    def run_step(self, cursor: int) -> CommandData | None | Err[CommandError | None]:
        """Advance the cursor by stepping over an unprocessed item."""
        result = self._rpc.raw_request("run_step", [cursor])
        if isinstance(result, Err):
            data = None if result.data is None else CommandError.from_dict(result.data)
            return Err(result.message, data)
        return None if result.result is None else CommandData.from_dict(result.result)
