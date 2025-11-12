from dataclasses import dataclass
from typing import Any, cast

from .rocq_doc_manager_raw import Err, RocqDocManagerRaw


@dataclass
class RocqSource:
    """Rocq source file information."""
    file: str
    dirpath: str | None

@dataclass
class RocqLoc:
    """Rocq source code location."""
    # End position.
    ep: int
    # Start position.
    bp: int
    # Position of the beginning of end line.
    bol_pos_last: int
    # End line number.
    line_nb_last: int
    # Position of the beginning of start line.
    bol_pos: int
    # Start line number.
    line_nb: int
    # Source file identification if not run as a toplevel.
    fname: RocqSource | None

@dataclass
class CommandData:
    """Data gathered while running a Rocq command."""
    # Inductives removed by the command.
    removed_inductives: list[str]
    # Inductives introduced by the command.
    new_inductives: list[str]
    # Constants removed by the command.
    removed_constants: list[str]
    # Constants introduced by the command.
    new_constants: list[str]
    # Open sub-goals, if in a proof.
    open_subgoals: str | None

@dataclass
class PrefixItem:
    """Document prefix item, appearing before the cursor."""
    text: str
    offset: int
    kind: str

@dataclass
class SuffixItem:
    """Document suffix item, appearing after the cursor."""
    text: str
    kind: str

@dataclass
class CompileResult:
    """Result of the `compile` method."""
    # Non-null if success is false.
    error: str | None
    stderr: str
    stdout: str
    success: bool

class RocqDocManagerAPI(RocqDocManagerRaw):

    def advance_to(self, index: int) -> None | Err[RocqLoc | None]:
        """Advance the cursor before the indicated unprocessed item."""
        result = self.request("advance_to", [index])
        if isinstance(result, Err):
            data = cast(RocqLoc | None, result.data)
            return Err(result.message, data)
        return cast(None, result)

    def clear_suffix(self) -> None:
        """Remove all unprocessed commands from the document."""
        result = self.request("clear_suffix", [])
        return cast(None, result)

    def commit(self, include_suffix: bool) -> None:
        """Write the current document contents to the file."""
        result = self.request("commit", [include_suffix])
        return cast(None, result)

    def compile(self) -> CompileResult:
        """Compile the current contents of the file with `rocq compile`."""
        result = self.request("compile", [])
        return cast(CompileResult, result)

    def cursor_index(self) -> int:
        """Gives the index at the cursor."""
        result = self.request("cursor_index", [])
        return cast(int, result)

    def doc_prefix(self) -> list[PrefixItem]:
        """Gives the list of all processed commands, appearing before the cursor."""
        result = self.request("doc_prefix", [])
        return cast(list[PrefixItem], result)

    def doc_suffix(self) -> list[SuffixItem]:
        """Gives the list of all unprocessed commands, appearing after the cursor."""
        result = self.request("doc_suffix", [])
        return cast(list[SuffixItem], result)

    def get_feedback(self) -> list[Any]:
        """Gets Rocq's feedback for the last run command (if any)."""
        result = self.request("get_feedback", [])
        return cast(list[Any], result)

    def go_to(self, index: int) -> None | Err[RocqLoc | None]:
        """Move the cursor right before the indicated item (whether it is already processed or not)."""
        result = self.request("go_to", [index])
        if isinstance(result, Err):
            data = cast(RocqLoc | None, result.data)
            return Err(result.message, data)
        return cast(None, result)

    def has_suffix(self) -> bool:
        """Indicates whether the document has a suffix (unprocessed items)."""
        result = self.request("has_suffix", [])
        return cast(bool, result)

    def insert_blanks(self, text: str) -> None:
        """Insert and process blanks at the cursor."""
        result = self.request("insert_blanks", [text])
        return cast(None, result)

    def insert_command(self, text: str) -> CommandData | Err[RocqLoc | None]:
        """Insert and process a command at the cursor."""
        result = self.request("insert_command", [text])
        if isinstance(result, Err):
            data = cast(RocqLoc | None, result.data)
            return Err(result.message, data)
        return cast(CommandData, result)

    def json_query(self, text: str, index: int) -> Any | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = self.request("json_query", [text, index])
        if isinstance(result, Err):
            data = cast(None, result.data)
            return Err(result.message, data)
        return cast(Any, result)

    def load_file(self) -> None | Err[RocqLoc | None]:
        """Adds the (unprocessed) file contents to the document (note that this requires running sentence-splitting, which requires the input file not to have syntax errors)."""
        result = self.request("load_file", [])
        if isinstance(result, Err):
            data = cast(RocqLoc | None, result.data)
            return Err(result.message, data)
        return cast(None, result)

    def revert_before(self, erase: bool, index: int) -> None:
        """Revert the cursor to an earlier point in the document."""
        result = self.request("revert_before", [erase, index])
        return cast(None, result)

    def run_command(self, text: str) -> CommandData | Err[None]:
        """Process a command at the cursor without inserting it in the document."""
        result = self.request("run_command", [text])
        if isinstance(result, Err):
            data = cast(None, result.data)
            return Err(result.message, data)
        return cast(CommandData, result)

    def run_step(self) -> CommandData | None | Err[RocqLoc | None]:
        """Advance the cursor by stepping over an unprocessed item."""
        result = self.request("run_step", [])
        if isinstance(result, Err):
            data = cast(RocqLoc | None, result.data)
            return Err(result.message, data)
        return cast(CommandData | None, result)

    def text_query(self, text: str, index: int) -> str | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = self.request("text_query", [text, index])
        if isinstance(result, Err):
            data = cast(None, result.data)
            return Err(result.message, data)
        return cast(str, result)

    def text_query_all(self, text: str, indices: list[int] | None) -> list[str] | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = self.request("text_query_all", [text, indices])
        if isinstance(result, Err):
            data = cast(None, result.data)
            return Err(result.message, data)
        return cast(list[str], result)
