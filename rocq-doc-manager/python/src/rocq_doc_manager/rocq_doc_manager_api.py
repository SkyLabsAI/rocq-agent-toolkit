from __future__ import annotations

# ruff: noqa: C416 -- unnecessary list comprehension
from typing import Any, Literal

from jsonrpc_tp import AsyncProtocol, Err, Error, Resp, SyncProtocol
from pydantic import BaseModel, Field

__all__ = [
    "RocqDocManagerAPI",
    "Err",
    "Error",
    "Resp",
    "CompileResult",
    "SuffixItem",
    "PrefixItem",
    "StepsError",
    "CommandError",
    "CommandData",
    "ProofState",
    "GlobrefsDiff",
    "FeedbackMessage",
    "Quickfix",
    "RocqLoc",
    "RocqSource",
]


class RocqSource(BaseModel):
    """Rocq source file information."""

    file: str = Field(
        kw_only=True,
    )
    dirpath: str | None = Field(
        kw_only=True,
        default=None,
    )


class RocqLoc(BaseModel):
    """Rocq source code location."""

    ep: int = Field(
        kw_only=True,
        description="end position",
    )
    bp: int = Field(
        kw_only=True,
        description="start position",
    )
    bol_pos_last: int = Field(
        kw_only=True,
        description="position of the beginning of end line",
    )
    line_nb_last: int = Field(
        kw_only=True,
        description="end line number",
    )
    bol_pos: int = Field(
        kw_only=True,
        description="position of the beginning of start line",
    )
    line_nb: int = Field(
        kw_only=True,
        description="start line number",
    )
    fname: RocqSource | None = Field(
        kw_only=True,
        default=None,
        description="source file identification if not run as a toplevel",
    )


class Quickfix(BaseModel):
    """Quick fix hint."""

    text: str = Field(
        kw_only=True,
    )
    loc: RocqLoc = Field(
        kw_only=True,
    )


class FeedbackMessage(BaseModel):
    """Rocq feedback message."""

    text: str = Field(
        kw_only=True,
    )
    quickfix: list[Quickfix] = Field(
        kw_only=True,
        default_factory=list,
    )
    loc: RocqLoc | None = Field(
        kw_only=True,
        default=None,
    )
    level: Literal["debug", "info", "notice", "warning", "error"] = Field(
        kw_only=True,
    )


class GlobrefsDiff(BaseModel):
    """Environment modification performed by a Rocq command."""

    removed_inductives: list[str] = Field(
        kw_only=True,
        default_factory=list,
    )
    added_inductives: list[str] = Field(
        kw_only=True,
        default_factory=list,
    )
    removed_constants: list[str] = Field(
        kw_only=True,
        default_factory=list,
    )
    added_constants: list[str] = Field(
        kw_only=True,
        default_factory=list,
    )


class ProofState(BaseModel):
    """Summary of a Rocq proof state, including the text of focused goals."""

    focused_goals: list[str] = Field(
        kw_only=True,
        default_factory=list,
    )
    unfocused_goals: list[int] = Field(
        kw_only=True,
        default_factory=list,
    )
    shelved_goals: int = Field(
        kw_only=True,
    )
    given_up_goals: int = Field(
        kw_only=True,
    )


class CommandData(BaseModel):
    """Data gathered while running a Rocq command."""

    proof_state: ProofState | None = Field(
        kw_only=True,
        default=None,
    )
    feedback_messages: list[FeedbackMessage] = Field(
        kw_only=True,
        default_factory=list,
    )
    globrefs_diff: GlobrefsDiff = Field(
        kw_only=True,
        default_factory=lambda: GlobrefsDiff(),
    )


class CommandError(BaseModel):
    """Data returned on Rocq command errors."""

    feedback_messages: list[FeedbackMessage] = Field(
        kw_only=True,
        default_factory=list,
    )
    error_loc: RocqLoc | None = Field(
        kw_only=True,
        default=None,
        description="optional source code location for the error",
    )


class StepsError(BaseModel):
    """Data returned by `run_steps`."""

    cmd_error: CommandError = Field(
        kw_only=True,
    )
    nb_processed: int = Field(
        kw_only=True,
        description="number of unprocessed items that were processed successfully",
    )


class PrefixItem(BaseModel):
    """Document prefix item, appearing before the cursor."""

    text: str = Field(
        kw_only=True,
    )
    offset: int = Field(
        kw_only=True,
    )
    kind: Literal["blanks", "command", "ghost"] = Field(
        kw_only=True,
    )


class SuffixItem(BaseModel):
    """Document suffix item, appearing after the cursor."""

    text: str = Field(
        kw_only=True,
    )
    kind: Literal["blanks", "command", "ghost"] = Field(
        kw_only=True,
    )


class CompileResult(BaseModel):
    """Result of the `compile` method."""

    error: str | None = Field(
        kw_only=True,
        default=None,
        description="non-null if success is false",
    )
    stderr: str = Field(
        kw_only=True,
    )
    stdout: str = Field(
        kw_only=True,
    )
    success: bool = Field(
        kw_only=True,
        default=False,
    )


class RocqDocManagerAPI:
    """Main API class."""

    def __init__(self, rpc: SyncProtocol) -> None:
        self._rpc: SyncProtocol = rpc

    def advance_to(
        self,
        cursor: int,
        index: int,
    ) -> None | Err[CommandError | None]:
        """Advance the cursor before the indicated unprocessed item."""
        result = self._rpc.raw_request(
            "advance_to",
            [cursor, index],
        )
        if isinstance(result, Err):
            data = None if result.data is None else CommandError.model_validate(result.data)
            return Err(result.message, data)
        return None

    def clear_suffix(
        self,
        cursor: int,
        count: int | None,
    ) -> None:
        """Remove unprocessed commands from the document."""
        result = self._rpc.raw_request(
            "clear_suffix",
            [cursor, count],
        )
        assert not isinstance(result, Err)
        return None

    def clone(
        self,
        cursor: int,
    ) -> int:
        """Clones the given cursor."""
        result = self._rpc.raw_request(
            "clone",
            [cursor],
        )
        assert not isinstance(result, Err)
        return int(result.result)

    def commit(
        self,
        cursor: int,
        file: str | None,
        include_ghost: bool,
        include_suffix: bool,
    ) -> None | Err[None]:
        """Write the current document contents to the file, failing in case of file system error."""
        result = self._rpc.raw_request(
            "commit",
            [cursor, file, include_ghost, include_suffix],
        )
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return None

    def compile(
        self,
        cursor: int,
    ) -> CompileResult:
        """Compile the current contents of the file with `rocq compile`."""
        result = self._rpc.raw_request(
            "compile",
            [cursor],
        )
        assert not isinstance(result, Err)
        return CompileResult.model_validate(result.result)

    def contents(
        self,
        cursor: int,
        include_ghost: bool,
        include_suffix: bool,
    ) -> str:
        """Gives the current contents of the document, as if it was written to a file."""
        result = self._rpc.raw_request(
            "contents",
            [cursor, include_ghost, include_suffix],
        )
        assert not isinstance(result, Err)
        return str(result.result)

    def copy_contents(
        self,
        src: int,
        dst: int,
    ) -> None:
        """Copies the contents of src into dst."""
        result = self._rpc.raw_request(
            "copy_contents",
            [src, dst],
        )
        assert not isinstance(result, Err)
        return None

    def cursor_index(
        self,
        cursor: int,
    ) -> int:
        """Gives the index at the cursor."""
        result = self._rpc.raw_request(
            "cursor_index",
            [cursor],
        )
        assert not isinstance(result, Err)
        return int(result.result)

    def dispose(
        self,
        cursor: int,
    ) -> None:
        """Destroys the cursor."""
        result = self._rpc.raw_request(
            "dispose",
            [cursor],
        )
        assert not isinstance(result, Err)
        return None

    def doc_prefix(
        self,
        cursor: int,
    ) -> list[PrefixItem]:
        """Gives the list of all processed commands, appearing before the cursor."""
        result = self._rpc.raw_request(
            "doc_prefix",
            [cursor],
        )
        assert not isinstance(result, Err)
        return [PrefixItem.model_validate(v1) for v1 in result.result]

    def doc_suffix(
        self,
        cursor: int,
    ) -> list[SuffixItem]:
        """Gives the list of all unprocessed commands, appearing after the cursor."""
        result = self._rpc.raw_request(
            "doc_suffix",
            [cursor],
        )
        assert not isinstance(result, Err)
        return [SuffixItem.model_validate(v1) for v1 in result.result]

    def dump(
        self,
        cursor: int,
    ) -> Any:
        """Dump the document contents (debug)."""
        result = self._rpc.raw_request(
            "dump",
            [cursor],
        )
        assert not isinstance(result, Err)
        return result.result

    def go_to(
        self,
        cursor: int,
        index: int,
    ) -> None | Err[CommandError | None]:
        """Move the cursor right before the indicated item (whether it is already processed or not)."""
        result = self._rpc.raw_request(
            "go_to",
            [cursor, index],
        )
        if isinstance(result, Err):
            data = None if result.data is None else CommandError.model_validate(result.data)
            return Err(result.message, data)
        return None

    def has_suffix(
        self,
        cursor: int,
    ) -> bool:
        """Indicates whether the document has a suffix (unprocessed items)."""
        result = self._rpc.raw_request(
            "has_suffix",
            [cursor],
        )
        assert not isinstance(result, Err)
        return bool(result.result)

    def insert_blanks(
        self,
        cursor: int,
        text: str,
    ) -> None:
        """Insert and process blanks at the cursor."""
        result = self._rpc.raw_request(
            "insert_blanks",
            [cursor, text],
        )
        assert not isinstance(result, Err)
        return None

    def insert_command(
        self,
        cursor: int,
        text: str,
    ) -> CommandData | Err[CommandError]:
        """Insert and process a command at the cursor."""
        result = self._rpc.raw_request(
            "insert_command",
            [cursor, text],
        )
        if isinstance(result, Err):
            data = CommandError.model_validate(result.data)
            return Err(result.message, data)
        return CommandData.model_validate(result.result)

    def load_file(
        self,
        cursor: int,
    ) -> None | Err[RocqLoc | None]:
        """Adds the (unprocessed) file contents to the document (note that this requires running sentence-splitting, which requires the input file not to have syntax errors)."""
        result = self._rpc.raw_request(
            "load_file",
            [cursor],
        )
        if isinstance(result, Err):
            data = None if result.data is None else RocqLoc.model_validate(result.data)
            return Err(result.message, data)
        return None

    def materialize(
        self,
        cursor: int,
    ) -> None | Err[None]:
        """Materializes the cursor, giving it its own dedicated top-level."""
        result = self._rpc.raw_request(
            "materialize",
            [cursor],
        )
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return None

    def query(
        self,
        cursor: int,
        text: str,
    ) -> CommandData | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = self._rpc.raw_request(
            "query",
            [cursor, text],
        )
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return CommandData.model_validate(result.result)

    def query_json(
        self,
        cursor: int,
        text: str,
        index: int,
    ) -> Any | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = self._rpc.raw_request(
            "query_json",
            [cursor, text, index],
        )
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return result.result

    def query_json_all(
        self,
        cursor: int,
        text: str,
        indices: list[int] | None,
    ) -> list[Any] | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = self._rpc.raw_request(
            "query_json_all",
            [cursor, text, indices],
        )
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return [v1 for v1 in result.result]

    def query_text(
        self,
        cursor: int,
        text: str,
        index: int,
    ) -> str | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = self._rpc.raw_request(
            "query_text",
            [cursor, text, index],
        )
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return str(result.result)

    def query_text_all(
        self,
        cursor: int,
        text: str,
        indices: list[int] | None,
    ) -> list[str] | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = self._rpc.raw_request(
            "query_text_all",
            [cursor, text, indices],
        )
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return [str(v1) for v1 in result.result]

    def revert_before(
        self,
        cursor: int,
        erase: bool,
        index: int,
    ) -> None:
        """Revert the cursor to an earlier point in the document."""
        result = self._rpc.raw_request(
            "revert_before",
            [cursor, erase, index],
        )
        assert not isinstance(result, Err)
        return None

    def run_command(
        self,
        cursor: int,
        text: str,
    ) -> CommandData | Err[None]:
        """Process a command at the cursor without inserting it in the document."""
        result = self._rpc.raw_request(
            "run_command",
            [cursor, text],
        )
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return CommandData.model_validate(result.result)

    def run_step(
        self,
        cursor: int,
    ) -> CommandData | None | Err[CommandError]:
        """Advance the cursor by stepping over an unprocessed item."""
        result = self._rpc.raw_request(
            "run_step",
            [cursor],
        )
        if isinstance(result, Err):
            data = CommandError.model_validate(result.data)
            return Err(result.message, data)
        return None if result.result is None else CommandData.model_validate(result.result)

    def run_steps(
        self,
        cursor: int,
        count: int,
    ) -> None | Err[StepsError]:
        """Advance the cursor by stepping over the given number of unprocessed item."""
        result = self._rpc.raw_request(
            "run_steps",
            [cursor, count],
        )
        if isinstance(result, Err):
            data = StepsError.model_validate(result.data)
            return Err(result.message, data)
        return None


class RocqDocManagerAPIAsync:
    """Main API class."""

    def __init__(self, rpc: AsyncProtocol) -> None:
        self._rpc: AsyncProtocol = rpc

    async def advance_to(
        self,
        cursor: int,
        index: int,
    ) -> None | Err[CommandError | None]:
        """Advance the cursor before the indicated unprocessed item."""
        result = await self._rpc.raw_request(
            "advance_to",
            [cursor, index],
        )
        if isinstance(result, Err):
            data = None if result.data is None else CommandError.model_validate(result.data)
            return Err(result.message, data)
        return None

    async def clear_suffix(
        self,
        cursor: int,
        count: int | None,
    ) -> None:
        """Remove unprocessed commands from the document."""
        result = await self._rpc.raw_request(
            "clear_suffix",
            [cursor, count],
        )
        assert not isinstance(result, Err)
        return None

    async def clone(
        self,
        cursor: int,
    ) -> int:
        """Clones the given cursor."""
        result = await self._rpc.raw_request(
            "clone",
            [cursor],
        )
        assert not isinstance(result, Err)
        return int(result.result)

    async def commit(
        self,
        cursor: int,
        file: str | None,
        include_ghost: bool,
        include_suffix: bool,
    ) -> None | Err[None]:
        """Write the current document contents to the file, failing in case of file system error."""
        result = await self._rpc.raw_request(
            "commit",
            [cursor, file, include_ghost, include_suffix],
        )
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return None

    async def compile(
        self,
        cursor: int,
    ) -> CompileResult:
        """Compile the current contents of the file with `rocq compile`."""
        result = await self._rpc.raw_request(
            "compile",
            [cursor],
        )
        assert not isinstance(result, Err)
        return CompileResult.model_validate(result.result)

    async def contents(
        self,
        cursor: int,
        include_ghost: bool,
        include_suffix: bool,
    ) -> str:
        """Gives the current contents of the document, as if it was written to a file."""
        result = await self._rpc.raw_request(
            "contents",
            [cursor, include_ghost, include_suffix],
        )
        assert not isinstance(result, Err)
        return str(result.result)

    async def copy_contents(
        self,
        src: int,
        dst: int,
    ) -> None:
        """Copies the contents of src into dst."""
        result = await self._rpc.raw_request(
            "copy_contents",
            [src, dst],
        )
        assert not isinstance(result, Err)
        return None

    async def cursor_index(
        self,
        cursor: int,
    ) -> int:
        """Gives the index at the cursor."""
        result = await self._rpc.raw_request(
            "cursor_index",
            [cursor],
        )
        assert not isinstance(result, Err)
        return int(result.result)

    async def dispose(
        self,
        cursor: int,
    ) -> None:
        """Destroys the cursor."""
        result = await self._rpc.raw_request(
            "dispose",
            [cursor],
        )
        assert not isinstance(result, Err)
        return None

    async def doc_prefix(
        self,
        cursor: int,
    ) -> list[PrefixItem]:
        """Gives the list of all processed commands, appearing before the cursor."""
        result = await self._rpc.raw_request(
            "doc_prefix",
            [cursor],
        )
        assert not isinstance(result, Err)
        return [PrefixItem.model_validate(v1) for v1 in result.result]

    async def doc_suffix(
        self,
        cursor: int,
    ) -> list[SuffixItem]:
        """Gives the list of all unprocessed commands, appearing after the cursor."""
        result = await self._rpc.raw_request(
            "doc_suffix",
            [cursor],
        )
        assert not isinstance(result, Err)
        return [SuffixItem.model_validate(v1) for v1 in result.result]

    async def dump(
        self,
        cursor: int,
    ) -> Any:
        """Dump the document contents (debug)."""
        result = await self._rpc.raw_request(
            "dump",
            [cursor],
        )
        assert not isinstance(result, Err)
        return result.result

    async def go_to(
        self,
        cursor: int,
        index: int,
    ) -> None | Err[CommandError | None]:
        """Move the cursor right before the indicated item (whether it is already processed or not)."""
        result = await self._rpc.raw_request(
            "go_to",
            [cursor, index],
        )
        if isinstance(result, Err):
            data = None if result.data is None else CommandError.model_validate(result.data)
            return Err(result.message, data)
        return None

    async def has_suffix(
        self,
        cursor: int,
    ) -> bool:
        """Indicates whether the document has a suffix (unprocessed items)."""
        result = await self._rpc.raw_request(
            "has_suffix",
            [cursor],
        )
        assert not isinstance(result, Err)
        return bool(result.result)

    async def insert_blanks(
        self,
        cursor: int,
        text: str,
    ) -> None:
        """Insert and process blanks at the cursor."""
        result = await self._rpc.raw_request(
            "insert_blanks",
            [cursor, text],
        )
        assert not isinstance(result, Err)
        return None

    async def insert_command(
        self,
        cursor: int,
        text: str,
    ) -> CommandData | Err[CommandError]:
        """Insert and process a command at the cursor."""
        result = await self._rpc.raw_request(
            "insert_command",
            [cursor, text],
        )
        if isinstance(result, Err):
            data = CommandError.model_validate(result.data)
            return Err(result.message, data)
        return CommandData.model_validate(result.result)

    async def load_file(
        self,
        cursor: int,
    ) -> None | Err[RocqLoc | None]:
        """Adds the (unprocessed) file contents to the document (note that this requires running sentence-splitting, which requires the input file not to have syntax errors)."""
        result = await self._rpc.raw_request(
            "load_file",
            [cursor],
        )
        if isinstance(result, Err):
            data = None if result.data is None else RocqLoc.model_validate(result.data)
            return Err(result.message, data)
        return None

    async def materialize(
        self,
        cursor: int,
    ) -> None | Err[None]:
        """Materializes the cursor, giving it its own dedicated top-level."""
        result = await self._rpc.raw_request(
            "materialize",
            [cursor],
        )
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return None

    async def query(
        self,
        cursor: int,
        text: str,
    ) -> CommandData | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = await self._rpc.raw_request(
            "query",
            [cursor, text],
        )
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return CommandData.model_validate(result.result)

    async def query_json(
        self,
        cursor: int,
        text: str,
        index: int,
    ) -> Any | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = await self._rpc.raw_request(
            "query_json",
            [cursor, text, index],
        )
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return result.result

    async def query_json_all(
        self,
        cursor: int,
        text: str,
        indices: list[int] | None,
    ) -> list[Any] | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = await self._rpc.raw_request(
            "query_json_all",
            [cursor, text, indices],
        )
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return [v1 for v1 in result.result]

    async def query_text(
        self,
        cursor: int,
        text: str,
        index: int,
    ) -> str | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = await self._rpc.raw_request(
            "query_text",
            [cursor, text, index],
        )
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return str(result.result)

    async def query_text_all(
        self,
        cursor: int,
        text: str,
        indices: list[int] | None,
    ) -> list[str] | Err[None]:
        """Runs the given query at the cursor, not updating the state."""
        result = await self._rpc.raw_request(
            "query_text_all",
            [cursor, text, indices],
        )
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return [str(v1) for v1 in result.result]

    async def revert_before(
        self,
        cursor: int,
        erase: bool,
        index: int,
    ) -> None:
        """Revert the cursor to an earlier point in the document."""
        result = await self._rpc.raw_request(
            "revert_before",
            [cursor, erase, index],
        )
        assert not isinstance(result, Err)
        return None

    async def run_command(
        self,
        cursor: int,
        text: str,
    ) -> CommandData | Err[None]:
        """Process a command at the cursor without inserting it in the document."""
        result = await self._rpc.raw_request(
            "run_command",
            [cursor, text],
        )
        if isinstance(result, Err):
            data = None
            return Err(result.message, data)
        return CommandData.model_validate(result.result)

    async def run_step(
        self,
        cursor: int,
    ) -> CommandData | None | Err[CommandError]:
        """Advance the cursor by stepping over an unprocessed item."""
        result = await self._rpc.raw_request(
            "run_step",
            [cursor],
        )
        if isinstance(result, Err):
            data = CommandError.model_validate(result.data)
            return Err(result.message, data)
        return None if result.result is None else CommandData.model_validate(result.result)

    async def run_steps(
        self,
        cursor: int,
        count: int,
    ) -> None | Err[StepsError]:
        """Advance the cursor by stepping over the given number of unprocessed item."""
        result = await self._rpc.raw_request(
            "run_steps",
            [cursor, count],
        )
        if isinstance(result, Err):
            data = StepsError.model_validate(result.data)
            return Err(result.message, data)
        return None
