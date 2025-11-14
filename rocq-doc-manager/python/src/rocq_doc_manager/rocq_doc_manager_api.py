# ruff: noqa: C416 -- unnecessary list comprehension
from dataclasses import dataclass, field
from typing import Any, TypeAlias

from jsonrpc_tp import JsonRPCTP


@dataclass
class RocqSource:
    """Rocq source file information."""
    file: str = field(kw_only=True, default="")
    dirpath: str | None = field(kw_only=True, default=None)

@dataclass
class RocqLoc:
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

@dataclass
class CommandData:
    """Data gathered while running a Rocq command."""
    # Inductives removed by the command.
    removed_inductives: list[str] = field(kw_only=True, default_factory=list)
    # Inductives introduced by the command.
    new_inductives: list[str] = field(kw_only=True, default_factory=list)
    # Constants removed by the command.
    removed_constants: list[str] = field(kw_only=True, default_factory=list)
    # Constants introduced by the command.
    new_constants: list[str] = field(kw_only=True, default_factory=list)
    # Open sub-goals, if in a proof.
    open_subgoals: str | None = field(kw_only=True, default=None)

@dataclass
class PrefixItem:
    """Document prefix item, appearing before the cursor."""
    text: str = field(kw_only=True, default="")
    offset: int = field(kw_only=True, default=0)
    kind: str = field(kw_only=True, default="")

@dataclass
class SuffixItem:
    """Document suffix item, appearing after the cursor."""
    text: str = field(kw_only=True, default="")
    kind: str = field(kw_only=True, default="")

@dataclass
class CompileResult:
    """Result of the `compile` method."""
    # Non-null if success is false.
    error: str | None = field(kw_only=True, default=None)
    stderr: str = field(kw_only=True, default="")
    stdout: str = field(kw_only=True, default="")
    success: bool = field(kw_only=True, default=False)

class RocqDocManagerAPI(JsonRPCTP):
    # NOTE: normally [type ... = ...] is preferred, but this cannot be used
    # with [isinstance].
    RocqSource: TypeAlias = RocqSource  # noqa: UP040
    RocqLoc: TypeAlias = RocqLoc  # noqa: UP040
    CommandData: TypeAlias = CommandData  # noqa: UP040
    PrefixItem: TypeAlias = PrefixItem  # noqa: UP040
    SuffixItem: TypeAlias = SuffixItem  # noqa: UP040
    CompileResult: TypeAlias = CompileResult  # noqa: UP040

    def advance_to(self, index: int) -> None | JsonRPCTP.Err[RocqLoc | None]:
        """Advance the cursor before the indicated unprocessed item."""
        result = self.raw_request("advance_to", [index])
        if isinstance(result, self.Err):
            data = None if result.data is None else RocqLoc(**result.data)
            return self.Err(result.message, data)
        return None

    def clear_suffix(self) -> None:
        """Remove all unprocessed commands from the document."""
        result = self.raw_request("clear_suffix", [])
        assert not isinstance(result, self.Err)
        return None

    def commit(self, include_suffix: bool) -> None:
        """Write the current document contents to the file."""
        result = self.raw_request("commit", [include_suffix])
        assert not isinstance(result, self.Err)
        return None

    def compile(self) -> CompileResult:
        """Compile the current contents of the file with `rocq compile`."""
        result = self.raw_request("compile", [])
        assert not isinstance(result, self.Err)
        return CompileResult(**result.result)

    def cursor_index(self) -> int:
        """Gives the index at the cursor."""
        result = self.raw_request("cursor_index", [])
        assert not isinstance(result, self.Err)
        return int(result.result)

    def doc_prefix(self) -> list[PrefixItem]:
        """Gives the list of all processed commands, appearing before the cursor."""
        result = self.raw_request("doc_prefix", [])
        assert not isinstance(result, self.Err)
        return [PrefixItem(**v1) for v1 in result.result]

    def doc_suffix(self) -> list[SuffixItem]:
        """Gives the list of all unprocessed commands, appearing after the cursor."""
        result = self.raw_request("doc_suffix", [])
        assert not isinstance(result, self.Err)
        return [SuffixItem(**v1) for v1 in result.result]

    def get_feedback(self) -> list[Any]:
        """Gets Rocq's feedback for the last run command (if any)."""
        result = self.raw_request("get_feedback", [])
        assert not isinstance(result, self.Err)
        return [v1 for v1 in result.result]

    def go_to(self, index: int) -> None | JsonRPCTP.Err[RocqLoc | None]:
        """Move the cursor right before the indicated item (whether it is already processed or not)."""
        result = self.raw_request("go_to", [index])
        if isinstance(result, self.Err):
            data = None if result.data is None else RocqLoc(**result.data)
            return self.Err(result.message, data)
        return None

    def has_suffix(self) -> bool:
        """Indicates whether the document has a suffix (unprocessed items)."""
        result = self.raw_request("has_suffix", [])
        assert not isinstance(result, self.Err)
        return bool(result.result)

    def insert_blanks(self, text: str) -> None:
        """Insert and process blanks at the cursor."""
        result = self.raw_request("insert_blanks", [text])
        assert not isinstance(result, self.Err)
        return None

    def insert_command(self, text: str) -> CommandData | JsonRPCTP.Err[RocqLoc | None]:
        """Insert and process a command at the cursor."""
        result = self.raw_request("insert_command", [text])
        if isinstance(result, self.Err):
            data = None if result.data is None else RocqLoc(**result.data)
            return self.Err(result.message, data)
        return CommandData(**result.result)

    def json_query(self, text: str, index: int) -> Any | JsonRPCTP.Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = self.raw_request("json_query", [text, index])
        if isinstance(result, self.Err):
            data = None
            return self.Err(result.message, data)
        return result.result

    def load_file(self) -> None | JsonRPCTP.Err[RocqLoc | None]:
        """Adds the (unprocessed) file contents to the document (note that this requires running sentence-splitting, which requires the input file not to have syntax errors)."""
        result = self.raw_request("load_file", [])
        if isinstance(result, self.Err):
            data = None if result.data is None else RocqLoc(**result.data)
            return self.Err(result.message, data)
        return None

    def revert_before(self, erase: bool, index: int) -> None:
        """Revert the cursor to an earlier point in the document."""
        result = self.raw_request("revert_before", [erase, index])
        assert not isinstance(result, self.Err)
        return None

    def run_command(self, text: str) -> CommandData | JsonRPCTP.Err[None]:
        """Process a command at the cursor without inserting it in the document."""
        result = self.raw_request("run_command", [text])
        if isinstance(result, self.Err):
            data = None
            return self.Err(result.message, data)
        return CommandData(**result.result)

    def run_step(self) -> CommandData | None | JsonRPCTP.Err[RocqLoc | None]:
        """Advance the cursor by stepping over an unprocessed item."""
        result = self.raw_request("run_step", [])
        if isinstance(result, self.Err):
            data = None if result.data is None else RocqLoc(**result.data)
            return self.Err(result.message, data)
        return None if result.result is None else CommandData(**result.result)

    def text_query(self, text: str, index: int) -> str | JsonRPCTP.Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = self.raw_request("text_query", [text, index])
        if isinstance(result, self.Err):
            data = None
            return self.Err(result.message, data)
        return str(result.result)

    def text_query_all(self, text: str, indices: list[int] | None) -> list[str] | JsonRPCTP.Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = self.raw_request("text_query_all", [text, indices])
        if isinstance(result, self.Err):
            data = None
            return self.Err(result.message, data)
        return [str(v1) for v1 in result.result]
