from dataclasses import dataclass
from typing import Any, cast

from .rocq_doc_manager_raw import Err, RocqDocManagerRaw


# Description: Rocq source file information.
@dataclass
class rocq_source:
    file: str
    dirpath: str | None

# Description: Rocq source code location.
@dataclass
class rocq_loc:
    # Description: end position.
    ep: int
    # Description: start position.
    bp: int
    # Description: position of the beginning of end line.
    bol_pos_last: int
    # Description: end line number.
    line_nb_last: int
    # Description: position of the beginning of start line.
    bol_pos: int
    # Description: start line number.
    line_nb: int
    # Description: source file identification if not run as a toplevel.
    fname: rocq_source | None

# Description: data gathered while running a Rocq command.
@dataclass
class command_data:
    # Description: inductives removed by the command.
    removed_inductives: list[str]
    # Description: inductives introduced by the command.
    new_inductives: list[str]
    # Description: constants removed by the command.
    removed_constants: list[str]
    # Description: constants introduced by the command.
    new_constants: list[str]
    # Description: open sub-goals, if in a proof.
    open_subgoals: str | None

# Description: document prefix item, appearing before the cursor.
@dataclass
class prefix_item:
    text: str
    offset: int
    kind: str

# Description: document suffix item, appearing after the cursor.
@dataclass
class suffix_item:
    text: str
    kind: str

# Description: result of the `compile` method.
@dataclass
class compile_result:
    # Description: non-null if success is false.
    error: str | None
    stderr: str
    stdout: str
    success: bool

class RocqDocManagerAPI(RocqDocManagerRaw):

    # Description: advance the cursor before the indicated unprocessed item.
    def advance_to(self, index: int) -> None | Err[rocq_loc | None]:
        result = self.request("advance_to", [index])
        if isinstance(result, Err):
            data = cast(rocq_loc | None, result.data)
            return Err(result.message, data)
        return cast(None, result)

    # Description: remove all unprocessed commands from the document.
    def clear_suffix(self) -> None:
        result = self.request("clear_suffix", [])
        return cast(None, result)

    # Description: write the current document contents to the file.
    def commit(self, include_suffix: bool) -> None:
        result = self.request("commit", [include_suffix])
        return cast(None, result)

    # Description: compile the current contents of the file with `rocq compile`.
    def compile(self) -> compile_result:
        result = self.request("compile", [])
        return cast(compile_result, result)

    # Description: gives the index at the cursor.
    def cursor_index(self) -> int:
        result = self.request("cursor_index", [])
        return cast(int, result)

    # Description: gives the list of all processed commands, appearing before the cursor.
    def doc_prefix(self) -> list[prefix_item]:
        result = self.request("doc_prefix", [])
        return cast(list[prefix_item], result)

    # Description: gives the list of all unprocessed commands, appearing after the cursor.
    def doc_suffix(self) -> list[suffix_item]:
        result = self.request("doc_suffix", [])
        return cast(list[suffix_item], result)

    # Description: gets Rocq's feedback for the last run command (if any).
    def get_feedback(self) -> list[Any]:
        result = self.request("get_feedback", [])
        return cast(list[Any], result)

    # Description: move the cursor right before the indicated item (whether it is already processed or not).
    def go_to(self, index: int) -> None | Err[rocq_loc | None]:
        result = self.request("go_to", [index])
        if isinstance(result, Err):
            data = cast(rocq_loc | None, result.data)
            return Err(result.message, data)
        return cast(None, result)

    # Description: indicates whether the document has a suffix (unprocessed items).
    def has_suffix(self) -> bool:
        result = self.request("has_suffix", [])
        return cast(bool, result)

    # Description: insert and process blanks at the cursor.
    def insert_blanks(self, text: str) -> None:
        result = self.request("insert_blanks", [text])
        return cast(None, result)

    # Description: insert and process a command at the cursor.
    def insert_command(self, text: str) -> command_data | Err[rocq_loc | None]:
        result = self.request("insert_command", [text])
        if isinstance(result, Err):
            data = cast(rocq_loc | None, result.data)
            return Err(result.message, data)
        return cast(command_data, result)

    # Description: runs the given query at the cursor, not updating the state.
    def json_query(self, text: str, index: int) -> Any | Err[None]:
        result = self.request("json_query", [text, index])
        if isinstance(result, Err):
            data = cast(None, result.data)
            return Err(result.message, data)
        return cast(Any, result)

    # Description: adds the (unprocessed) file contents to the document (note that this requires running sentence-splitting, which requires the input file not to have syntax errors).
    def load_file(self) -> None | Err[rocq_loc | None]:
        result = self.request("load_file", [])
        if isinstance(result, Err):
            data = cast(rocq_loc | None, result.data)
            return Err(result.message, data)
        return cast(None, result)

    # Description: revert the cursor to an earlier point in the document.
    def revert_before(self, erase: bool, index: int) -> None:
        result = self.request("revert_before", [erase, index])
        return cast(None, result)

    # Description: process a command at the cursor without inserting it in the document.
    def run_command(self, text: str) -> command_data | Err[None]:
        result = self.request("run_command", [text])
        if isinstance(result, Err):
            data = cast(None, result.data)
            return Err(result.message, data)
        return cast(command_data, result)

    # Description: advance the cursor by stepping over an unprocessed item.
    def run_step(self) -> command_data | None | Err[rocq_loc | None]:
        result = self.request("run_step", [])
        if isinstance(result, Err):
            data = cast(rocq_loc | None, result.data)
            return Err(result.message, data)
        return cast(command_data | None, result)

    # Description: runs the given query at the cursor, not updating the state.
    def text_query(self, text: str, index: int) -> str | Err[None]:
        result = self.request("text_query", [text, index])
        if isinstance(result, Err):
            data = cast(None, result.data)
            return Err(result.message, data)
        return cast(str, result)

    # Description: runs the given query at the cursor, not updating the state.
    def text_query_all(self, text: str, indices: list[int] | None) -> list[str] | Err[None]:
        result = self.request("text_query_all", [text, indices])
        if isinstance(result, Err):
            data = cast(None, result.data)
            return Err(result.message, data)
        return cast(list[str], result)
