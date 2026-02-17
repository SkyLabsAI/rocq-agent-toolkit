from __future__ import annotations

import logging
from collections.abc import AsyncIterator, Callable, Iterator
from contextlib import asynccontextmanager, contextmanager
from typing import Any, Literal, Protocol, Self

from . import rocq_doc_manager_api as rdm_api
from .decorators import ensure_endswith_period

logger = logging.getLogger(__name__)


class RocqCursorProtocolAsync(Protocol):
    async def advance_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]: ...

    async def clear_suffix(self, count: int | None = None) -> None: ...

    async def materialize(self) -> None:
        """Enable parallel processing on this cursor."""
        ...

    async def clone(self, *, materialize: bool = False) -> RocqCursorProtocolAsync: ...

    async def commit(
        self,
        file: str | None,
        *,
        include_ghost: bool = False,
        include_suffix: bool = True,
    ) -> None | rdm_api.Err[None]: ...

    async def compile(self) -> rdm_api.CompileResult: ...

    async def cursor_index(self) -> int: ...

    async def dispose(self) -> None: ...

    async def doc_prefix(self) -> list[rdm_api.PrefixItem]: ...

    async def doc_suffix(self) -> list[rdm_api.SuffixItem]: ...

    async def go_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]: ...

    async def has_suffix(self) -> bool: ...

    async def insert_blanks(self, text: str) -> None: ...

    async def _insert_command(
        self, text: str
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]: ...

    @ensure_endswith_period(argnames="text")
    async def insert_command(
        self, text: str, blanks: str | None = "\n", safe: bool = True
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        if safe:
            prefix = await self.doc_prefix()
            if prefix != [] and prefix[-1].kind != "blanks":
                await self.insert_blanks(" ")
                revert = True
            else:
                revert = False
        else:
            revert = False

        try:
            result = await self._insert_command(text)
            if isinstance(result, rdm_api.CommandError):
                if revert:
                    await self.revert_before(erase=True, index=len(prefix))
            elif blanks is not None:
                await self.insert_blanks(blanks)
            return result
        except rdm_api.Error:
            if revert:
                await self.revert_before(erase=True, index=len(prefix))
            raise

    async def load_file(
        self,
    ) -> None | rdm_api.Err[rdm_api.RocqLoc | None]: ...

    # TODO: we should really reduce the repetition on [query],
    # there are 5 functions, but they all do basically the same thing
    async def query(self, text: str) -> rdm_api.CommandData | rdm_api.Err[None]: ...

    async def query_json(self, text: str, *, index: int) -> Any | rdm_api.Err[None]: ...

    async def query_json_all(
        self, text: str, *, indices: list[int] | None
    ) -> list[Any] | rdm_api.Err[None]: ...

    async def query_text(self, text: str, *, index: int) -> str | rdm_api.Err[None]: ...

    async def query_text_all(
        self, text: str, *, indices: list[int] | None
    ) -> list[str] | rdm_api.Err[None]: ...

    async def revert_before(
        self, erase: bool, index: int
    ) -> None | rdm_api.Err[None]: ...

    async def run_command(
        self, text: str
    ) -> rdm_api.CommandData | rdm_api.Err[None]: ...

    async def run_step(
        self,
    ) -> rdm_api.CommandData | None | rdm_api.Err[rdm_api.CommandError | None]: ...

    # ===== BEGIN: contextmanagers ============================================
    @asynccontextmanager
    async def ctx(self, rollback: bool = True) -> AsyncIterator[Self]:
        """Base RDM context manager supporting optional doc rollback."""
        current_idx: int = 0  # satisfies pyright.
        if rollback:
            current_idx = await self.cursor_index()
            # NOTE: blanks are fused, so inserting blanks at the beginning
            # of a rollback context can leave the document in a modified state.
            # By inserting a real (but trivial) command that we rollback, we
            # ensure that the document is left unchanged.
            marker_cmd = "Check tt."
            insert_command_reply = await self.insert_command(marker_cmd)
            if isinstance(insert_command_reply, rdm_api.Err):
                raise rdm_api.Error(
                    " ".join(
                        [
                            f"RocqDocManager failed to insert {marker_cmd}:",
                            str(insert_command_reply),
                        ]
                    )
                )

        yield self

        if rollback:
            revert_reply = await self.revert_before(True, current_idx)
            if isinstance(revert_reply, rdm_api.Err):
                raise rdm_api.Error(
                    " ".join(
                        [
                            "RocqDocManager failed to rollback to",
                            f"{current_idx}: {revert_reply}",
                        ]
                    )
                )

    @asynccontextmanager
    async def aborted_goal_ctx(
        self, goal: str = "True", rollback: bool = True
    ) -> AsyncIterator[Self]:
        """RDM context manager that sets up an aborted goal."""
        async with self.ctx(rollback=rollback):
            goal_reply = self.insert_command(f"Goal {goal}.")
            if isinstance(goal_reply, rdm_api.Err):
                raise rdm_api.Error(goal_reply)

            yield self

            abort_reply = self.insert_command("Abort.")
            if isinstance(abort_reply, rdm_api.Err):
                raise rdm_api.Error(abort_reply)

    # NOTE: we could expose a more structured way to build the context list.
    @asynccontextmanager
    async def Section(
        self,
        name: str,
        context: list[str] | None = None,
        rollback: bool = False,
    ) -> AsyncIterator[Self]:
        async with self.ctx(rollback=rollback):
            begin_section_reply = self.insert_command(f"Section {name}.")
            if isinstance(begin_section_reply, rdm_api.Err):
                raise rdm_api.Error(begin_section_reply)

            if context is not None:
                context_reply = self.insert_command(f"Context {' '.join(context)}.")
                if isinstance(context_reply, rdm_api.Err):
                    raise rdm_api.Error(context_reply)

            yield self

            end_section_reply = self.insert_command(f"End {name}.")
            if isinstance(end_section_reply, rdm_api.Err):
                raise rdm_api.Error(end_section_reply)

    # ===== END: contextmanagers ==============================================

    # ===== BEGIN: visitors ===================================================
    # TODOS:
    # - expose smarter and more efficient visitors (e.g. skipping
    #   non side-effecting proof sentences, batching visits, etc...)
    # - update rocq-doc-manager API to reflect that kind must be
    #   "command" or "blanks".
    async def goto_first_match(
        self,
        fn: Callable[[str, Literal["blanks", "command", "ghost"]], bool],
        skip: int = 0,
        include_prefix: bool = False,
        step_over_match: bool = False,
    ) -> bool:
        """Move to the first matching point after the current cursor location.

        Arguments:
            skip: the number of matches to skip, e.g. `skip=1` will go to the second match.
            include_prefix: include matches in the prefix
            step_over_match: step over the matching line
        Returns:
            True if the target match is found, False otherwise. If `False` is
            returned due to moving the cursor, the cursor may be in an arbitrary
            location.
        """
        prefix = await self.doc_prefix()
        suffix = await self.doc_suffix()

        candidate_prefix_matches = [
            (idx, item.text)
            for idx, item in enumerate(prefix)
            if fn(item.text, item.kind)
        ]
        candidate_suffix_matches = [
            (idx + len(prefix), item.text)
            for idx, item in enumerate(suffix)
            if fn(item.text, item.kind)
        ]

        async def check_result(
            result: rdm_api.Err | object, mtch: tuple[int, str]
        ) -> bool:
            if isinstance(result, rdm_api.Err):
                logger.warning(
                    " ".join(
                        [
                            f"Failed to advance to the match ({mtch[1]} @ idx {mtch[0]}):",
                            str(advance_to_reply),
                        ]
                    )
                )
                return False
            if step_over_match:
                run_step_reply = await self.run_step()
                if isinstance(run_step_reply, rdm_api.Err):
                    logger.warning(
                        "Failed to step over the match: {run_step_repl}",
                    )
                    return False
            return True

        if include_prefix:
            if skip < len(candidate_prefix_matches):
                # Use this match
                return await check_result(
                    await self.go_to(candidate_prefix_matches[skip][0]),
                    candidate_prefix_matches[skip],
                )
            else:
                skip -= len(candidate_prefix_matches)

        if len(candidate_suffix_matches) <= skip:
            return False

        advance_to_reply = await self.advance_to(candidate_suffix_matches[skip][0])
        return await check_result(advance_to_reply, candidate_suffix_matches[skip])

    # ===== END: visitors =====================================================

    # ===== BEGIN: macros =====================================================
    async def Compute(
        self,
        term: str,
        rollback: bool = True,
    ) -> (
        tuple[str, str]
        | rdm_api.Err[rdm_api.CommandError]
        | rdm_api.Err[list[str]]
        | rdm_api.Err[None]
    ):
        """Run [Compute {term}.] and return the resulting value and type.

        Arguments:
            - term (str): the term to compute
            - rollback (bool=True): whether to rollback the command

        Raises:
            - RocqDocManager.Error: if inserting the requested command fails

        Returns:
            - a tuple containing:
                - the computed value
                - the type of the computed value
        """
        async with self.aborted_goal_ctx(
            goal=f"exists v, v = ({term})", rollback=rollback
        ):
            command_reply = await self.insert_command("vm_compute.")
            if isinstance(command_reply, rdm_api.Err):
                return command_reply

            query_reply = await self.query_text_all(
                """match goal with
                | |- context[@ex ?TY (fun x => x = ?RESULT)] => idtac RESULT; idtac TY
                end.""",
                indices=None,
            )
            if isinstance(query_reply, rdm_api.Err):
                return query_reply

            if len(query_reply) != 2:
                return rdm_api.Err(
                    message="RocqDocManager.Compute: expected a term and type",
                    data=query_reply,
                )

            return (query_reply[0], query_reply[1])

    async def current_goal(self) -> rdm_api.ProofState | None:
        result = await self.query("About nat.")
        assert not isinstance(result, rdm_api.Err)
        return result.proof_state

    async def _import_export_cmd(
        self,
        kind: Literal["Import", "Export"],
        logpath: str,
        require: bool = True,
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        cmd: str = f"{'Require ' if require else ''}{kind} {logpath}."
        return await self.insert_command(cmd)

    async def Import(
        self,
        logpath: str,
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return await self._import_export_cmd("Import", logpath, require=False)

    async def Export(
        self,
        logpath: str,
        require: bool = True,
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return await self._import_export_cmd("Export", logpath, require=False)

    async def RequireImport(
        self,
        logpath: str,
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return await self._import_export_cmd("Import", logpath, require=True)

    async def RequireExport(
        self,
        logpath: str,
        require: bool = True,
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return await self._import_export_cmd("Export", logpath, require=True)

    async def fresh_ident(self, ident: str) -> str | rdm_api.Err[None]:
        """Return a fresh name based on [ident].

        Arguments:
            - mgr (RocqDocManager): the document manager to send the request to
            - ident (str): the base for the fresh name

        Raises:
            - RocqDocManager.Error: if inserting the requested command fails.

        Returns:
            - a Rocq name which is guaranteed to be fresh at the
                  current loc. within [mgr]
        """
        result = await self.query_text(
            f'Eval lazy in ltac:(let nm := fresh "{ident}" in idtac nm).', index=0
        )
        if isinstance(result, rdm_api.Err):
            return rdm_api.Err("Not in proof mode", None)
        return result

    # ===== END: macros =======================================================

    # ===== BEGIN: contextmanagers ============================================
    @asynccontextmanager
    async def sess(self) -> AsyncIterator[Self]:
        yield self
        await self.dispose()

    # ===== END: contextmanagers ===============================================


class RocqCursorProtocolSync(Protocol):
    """
    Cursors represent a pointer into a Rocq document.
    """

    def advance_to_sync(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]: ...

    def clear_suffix_sync(self, count: int | None = None) -> None: ...

    def materialize_sync(self) -> None:
        """Enable parallel processing on this cursor."""
        ...

    def clone_sync(self, *, materialize: bool = False) -> RocqCursor: ...

    def commit_sync(
        self,
        file: str | None,
        *,
        include_ghost: bool = False,
        include_suffix: bool = True,
    ) -> None | rdm_api.Err[None]: ...

    def compile_sync(self) -> rdm_api.CompileResult: ...

    def cursor_index_sync(self) -> int: ...

    def dispose_sync(self) -> None: ...

    def doc_prefix_sync(self) -> list[rdm_api.PrefixItem]: ...

    def doc_suffix_sync(self) -> list[rdm_api.SuffixItem]: ...

    def go_to_sync(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]: ...

    def has_suffix_sync(self) -> bool: ...

    def insert_blanks_sync(self, text: str) -> None: ...

    def _insert_command_sync(
        self, text: str
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]: ...

    @ensure_endswith_period(argnames="text")
    def insert_command_sync(
        self, text: str, blanks: str | None = "\n", safe: bool = True
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        if safe:
            prefix = self.doc_prefix_sync()
            if prefix != [] and prefix[-1].kind != "blanks":
                self.insert_blanks_sync(" ")
                revert = True
            else:
                revert = False
        else:
            revert = False

        try:
            result = self._insert_command_sync(text)
            if isinstance(result, rdm_api.CommandError):
                if revert:
                    self.revert_before_sync(erase=True, index=len(prefix))
            elif blanks is not None:
                self.insert_blanks_sync(blanks)
            return result
        except rdm_api.Error:
            if revert:
                self.revert_before_sync(erase=True, index=len(prefix))
            raise

    def load_file_sync(
        self,
    ) -> None | rdm_api.Err[rdm_api.RocqLoc | None]: ...

    # TODO: we should really reduce the repetition on [query],
    # there are 5 functions, but they all do basically the same thing
    def query_sync(self, text: str) -> rdm_api.CommandData | rdm_api.Err[None]: ...

    def query_json_sync(self, text: str, *, index: int) -> Any | rdm_api.Err[None]: ...

    def query_json_all_sync(
        self, text: str, *, indices: list[int] | None
    ) -> list[Any] | rdm_api.Err[None]: ...

    def query_text_sync(self, text: str, *, index: int) -> str | rdm_api.Err[None]: ...

    def query_text_all_sync(
        self, text: str, *, indices: list[int] | None
    ) -> list[str] | rdm_api.Err[None]: ...

    def revert_before_sync(
        self, erase: bool, index: int
    ) -> None | rdm_api.Err[None]: ...

    def run_command_sync(
        self, text: str
    ) -> rdm_api.CommandData | rdm_api.Err[None]: ...

    def run_step_sync(
        self,
    ) -> rdm_api.CommandData | None | rdm_api.Err[rdm_api.CommandError]: ...

    def run_steps_sync(self, count: int) -> None | rdm_api.Err[rdm_api.StepsError]: ...

    # ===== BEGIN: contextmanagers ============================================
    @contextmanager
    def ctx_sync(self, rollback: bool = True) -> Iterator[Self]:
        """Base RDM context manager supporting optional doc rollback."""
        current_idx: int = 0  # satisfies pyright.
        if rollback:
            current_idx = self.cursor_index_sync()
            # NOTE: blanks are fused, so inserting blanks at the beginning
            # of a rollback context can leave the document in a modified state.
            # By inserting a real (but trivial) command that we rollback, we
            # ensure that the document is left unchanged.
            marker_cmd = "Check tt."
            insert_command_reply = self.insert_command_sync(marker_cmd)
            if isinstance(insert_command_reply, rdm_api.Err):
                raise rdm_api.Error(
                    " ".join(
                        [
                            f"RocqDocManager failed to insert {marker_cmd}:",
                            str(insert_command_reply),
                        ]
                    )
                )

        yield self

        if rollback:
            revert_reply = self.revert_before_sync(True, current_idx)
            if isinstance(revert_reply, rdm_api.Err):
                raise rdm_api.Error(
                    " ".join(
                        [
                            "RocqDocManager failed to rollback to",
                            f"{current_idx}: {revert_reply}",
                        ]
                    )
                )

    @contextmanager
    def aborted_goal_ctx_sync(
        self, goal: str = "True", rollback: bool = True
    ) -> Iterator[Self]:
        """RDM context manager that sets up an aborted goal."""
        with self.ctx_sync(rollback=rollback):
            goal_reply = self.insert_command_sync(f"Goal {goal}.")
            if isinstance(goal_reply, rdm_api.Err):
                raise rdm_api.Error(goal_reply)

            yield self

            abort_reply = self.insert_command_sync("Abort.")
            if isinstance(abort_reply, rdm_api.Err):
                raise rdm_api.Error(abort_reply)

    # NOTE: we could expose a more structured way to build the context list.
    @contextmanager
    def Section_sync(
        self,
        name: str,
        context: list[str] | None = None,
        rollback: bool = False,
    ) -> Iterator[Self]:
        with self.ctx_sync(rollback=rollback):
            begin_section_reply = self.insert_command_sync(f"Section {name}.")
            if isinstance(begin_section_reply, rdm_api.Err):
                raise rdm_api.Error(begin_section_reply)

            if context is not None:
                context_reply = self.insert_command_sync(
                    f"Context {' '.join(context)}."
                )
                if isinstance(context_reply, rdm_api.Err):
                    raise rdm_api.Error(context_reply)

            yield self

            end_section_reply = self.insert_command_sync(f"End {name}.")
            if isinstance(end_section_reply, rdm_api.Err):
                raise rdm_api.Error(end_section_reply)

    # ===== END: contextmanagers ==============================================

    # ===== BEGIN: visitors ===================================================
    # TODOS:
    # - expose smarter and more efficient visitors (e.g. skipping
    #   non side-effecting proof sentences, batching visits, etc...)
    # - update rocq-doc-manager API to reflect that kind must be
    #   "command" or "blanks".
    def goto_first_match_sync(
        self,
        fn: Callable[[str, Literal["blanks", "command", "ghost"]], bool],
        skip: int = 0,
        include_prefix: bool = False,
        step_over_match: bool = False,
    ) -> bool:
        """Move to the first matching point after the current cursor location.

        Arguments:
            skip: the number of matches to skip, e.g. `skip=1` will go to the second match.
            include_prefix: include matches in the prefix
            step_over_match: step over the matching line
        Returns:
            True if the target match is found, False otherwise. If `False` is
            returned due to moving the cursor, the cursor may be in an arbitrary
            location.
        """
        prefix = self.doc_prefix_sync()
        suffix = self.doc_suffix_sync()

        candidate_prefix_matches = [
            (idx, item.text)
            for idx, item in enumerate(prefix)
            if fn(item.text, item.kind)
        ]
        candidate_suffix_matches = [
            (idx + len(prefix), item.text)
            for idx, item in enumerate(suffix)
            if fn(item.text, item.kind)
        ]

        def check_result_sync(
            result: rdm_api.Err | object, mtch: tuple[int, str]
        ) -> bool:
            if isinstance(result, rdm_api.Err):
                logger.warning(
                    " ".join(
                        [
                            f"Failed to advance to the match ({mtch[1]} @ idx {mtch[0]}):",
                            str(advance_to_reply),
                        ]
                    )
                )
                return False
            if step_over_match:
                run_step_reply = self.run_step_sync()
                if isinstance(run_step_reply, rdm_api.Err):
                    logger.warning(
                        "Failed to step over the match: {run_step_repl}",
                    )
                    return False
            return True

        if include_prefix:
            if skip < len(candidate_prefix_matches):
                # Use this match
                return check_result_sync(
                    self.go_to_sync(candidate_prefix_matches[skip][0]),
                    candidate_prefix_matches[skip],
                )
            else:
                skip -= len(candidate_prefix_matches)

        if len(candidate_suffix_matches) <= skip:
            return False

        advance_to_reply = self.advance_to_sync(candidate_suffix_matches[skip][0])
        return check_result_sync(advance_to_reply, candidate_suffix_matches[skip])

    # ===== END: visitors =====================================================

    # ===== BEGIN: macros =====================================================
    def Compute_sync(
        self,
        term: str,
        rollback: bool = True,
    ) -> (
        tuple[str, str]
        | rdm_api.Err[rdm_api.CommandError]
        | rdm_api.Err[list[str]]
        | rdm_api.Err[None]
    ):
        """Run [Compute {term}.] and return the resulting value and type.

        Arguments:
            - term (str): the term to compute
            - rollback (bool=True): whether to rollback the command

        Raises:
            - RocqDocManager.Error: if inserting the requested command fails

        Returns:
            - a tuple containing:
                - the computed value
                - the type of the computed value
        """
        with self.aborted_goal_ctx_sync(
            goal=f"exists v, v = ({term})", rollback=rollback
        ):
            command_reply = self.insert_command_sync("vm_compute.")
            if isinstance(command_reply, rdm_api.Err):
                return command_reply

            query_reply = self.query_text_all_sync(
                """match goal with
                | |- context[@ex ?TY (fun x => x = ?RESULT)] => idtac RESULT; idtac TY
                end.""",
                indices=None,
            )
            if isinstance(query_reply, rdm_api.Err):
                return query_reply

            if len(query_reply) != 2:
                return rdm_api.Err(
                    message="RocqDocManager.Compute: expected a term and type",
                    data=query_reply,
                )

            return (query_reply[0], query_reply[1])

    def current_goal_sync(self) -> rdm_api.ProofState | None:
        result = self.query_sync("About nat.")
        assert not isinstance(result, rdm_api.Err)
        return result.proof_state

    def _import_export_cmd_sync(
        self,
        kind: Literal["Import"] | Literal["Export"],
        logpath: str,
        require: bool = True,
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        cmd: str = f"{'Require ' if require else ''}{kind} {logpath}."
        return self.insert_command_sync(cmd)

    def Import_sync(
        self,
        logpath: str,
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return self._import_export_cmd_sync("Import", logpath, require=False)

    def Export_sync(
        self,
        logpath: str,
        require: bool = True,
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return self._import_export_cmd_sync("Export", logpath, require=False)

    def RequireImport_sync(
        self,
        logpath: str,
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return self._import_export_cmd_sync("Import", logpath, require=True)

    def RequireExport_sync(
        self,
        logpath: str,
        require: bool = True,
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return self._import_export_cmd_sync("Export", logpath, require=True)

    def fresh_ident_sync(self, ident: str) -> str | rdm_api.Err[None]:
        """Return a fresh name based on [ident].

        Arguments:
            - mgr (RocqDocManager): the document manager to send the request to
            - ident (str): the base for the fresh name

        Raises:
            - RocqDocManager.Error: if inserting the requested command fails.

        Returns:
            - a Rocq name which is guaranteed to be fresh at the
                  current loc. within [mgr]
        """
        result = self.query_text_sync(
            f'Eval lazy in ltac:(let nm := fresh "{ident}" in idtac nm).', index=0
        )
        if isinstance(result, rdm_api.Err):
            return rdm_api.Err("Not in proof mode", None)
        return result

    # ===== END: macros =======================================================

    # ===== BEGIN: contextmanagers ============================================
    @contextmanager
    def sess_sync(self) -> Iterator[Self]:
        yield self
        self.dispose_sync()

    # ===== END: contextmanagers ===============================================


class RocqCursor(RocqCursorProtocolAsync, Protocol):
    # TODO: Add the Sync protocol here as well?
    """A RocqCursor represents a cursor into a Rocq document."""

    ...


# class FromAsync(RocqCursor):
#     """Build a full RocqCursor from an asynchronous RocqCursor"""

#     def __init__(self, async_cursor: RocqCursorProtocolAsync) -> None:
#         self._async_cursor = async_cursor


# class FromSync(RocqCursor):
#     """Build a full RocqCursor from a synchronous RocqCursor"""

#     def __init__(self, sync_cursor: RocqCursorProtocolSync) -> None:
#         self._sync_cursor = sync_cursor


# class Delegate(RocqCursor):
#     """Delegate the entire RocqCursor interface."""

#     def __init__(self, target: RocqCursor) -> None:
#         self._target = target
