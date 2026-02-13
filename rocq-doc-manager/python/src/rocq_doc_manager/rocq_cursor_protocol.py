from __future__ import annotations

import functools
import inspect
import logging
from collections.abc import Callable, Collection, Iterator
from contextlib import contextmanager
from types import FunctionType
from typing import Any, Literal, Protocol, Self, cast, get_type_hints

from . import rocq_doc_manager_api as rdm_api

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

    async def insert_command(
        self, text: str
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]: ...

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


class RocqCursor(Protocol):
    """
    Cursors represent a pointer into a Rocq document.
    """

    @staticmethod
    def ensure_return_endswith_period[**P, T](fn: Callable[P, T]) -> Callable[P, T]:
        """Decorator: ensure that the return value ends with a period."""
        return RocqCursor.ensure_endswith_period(argnames=None, return_=True)(fn)

    # TODO: simplify this with use of `wrapt` once opentelemetry-python-contrib
    # relaxes too-strict version constraints.
    #
    # cf. https://github.com/open-telemetry/opentelemetry-python-contrib/pull/3930
    @staticmethod
    def ensure_endswith_period[**P, T](
        *,
        argnames: Collection[str] | str | None = None,
        return_: bool = False,
    ) -> Callable[[Callable[P, T]], Callable[P, T]]:
        """Decorator: ensure that named arguments and/or return type end with period.

        If a named argument or return value doesn't end with a period, emit a `logger.warning`.

        Args:
            maybe_fn: The function to decorate, or None if used as @decorator()
            argnames: Collection of argument names to check, or a single string.
                     If None, no arguments are checked.
                     If a string, converted to [string].
            return_: If True, check that the return value ends with a period.

        Examples:
            @ensure_endswith_period(argnames="text")  # single string
            @ensure_endswith_period(argnames=["text"])  # list
            @ensure_endswith_period(argnames=["text1", "text2"])  # multiple
            @ensure_endswith_period(return_=True)  # check return type
            @ensure_endswith_period(argnames="text", return_=True)  # both
        """
        # Validate that at least one check is requested
        if argnames is None and not return_:
            raise ValueError(
                "RocqCursorProtocol.ensure_endswith_period: "
                "at least one of argnames or return_ must be specified. "
                "The decorator is a useless no-op if both are None/False."
            )

        # Normalize argnames
        if argnames is not None:
            if isinstance(argnames, str):
                argnames_set = {argnames}
            else:
                argnames_set = set(argnames)

            if not argnames_set:
                raise ValueError(
                    "RocqCursorProtocol.ensure_endswith_period: argnames empty"
                )
        else:
            argnames_set = None

        @functools.cache
        def _validated_signature(fn: Callable[P, T]) -> inspect.Signature:
            signature = inspect.signature(fn)

            assert isinstance(fn, FunctionType)

            # Validate argument names if specified
            if argnames_set is not None:
                fn_argnames = signature.parameters.keys()
                missing_argnames = argnames_set - fn_argnames
                if missing_argnames:
                    raise ValueError(
                        f"{missing_argnames} not found in parameters of "
                        f"{fn.__name__}: {signature}"
                    )

                for argname in argnames_set:
                    param = signature.parameters[argname]
                    if (
                        param.annotation is not None
                        and param.annotation is not inspect.Parameter.empty
                    ):
                        # Resolve string annotations (from __future__ import annotations)
                        # Try to get resolved type hints, fallback to annotation if it fails
                        try:
                            type_hints = get_type_hints(fn, include_extras=False)
                            resolved_annotation = type_hints.get(
                                argname, param.annotation
                            )
                        except Exception:
                            # If get_type_hints fails, use the annotation as-is
                            resolved_annotation = param.annotation

                        # Check if annotation is str type (handle both str type and "str" string)
                        if (
                            resolved_annotation is not str
                            and resolved_annotation != "str"
                        ):
                            raise ValueError(
                                f"parameter {argname} of {fn.__name__} "
                                f"should be str: {resolved_annotation}"
                            )

            # Validate return type if specified
            if return_:
                return_annotation = signature.return_annotation
                if (
                    return_annotation is not None
                    and return_annotation is not inspect.Signature.empty
                ):
                    # Resolve string annotations
                    try:
                        type_hints = get_type_hints(fn, include_extras=False)
                        resolved_annotation = type_hints.get(
                            "return", return_annotation
                        )
                    except Exception:
                        resolved_annotation = return_annotation

                    # Check if annotation is str type
                    if resolved_annotation is not str and resolved_annotation != "str":
                        raise ValueError(
                            f"return type of {fn.__name__} "
                            f"should be str: {resolved_annotation}"
                        )

            return signature

        def decorator(fn: Callable[P, T]) -> Callable[P, T]:
            signature = _validated_signature(fn)

            @functools.wraps(fn)
            def _wrapped(*args: P.args, **kwargs: P.kwargs) -> T:
                assert isinstance(fn, FunctionType)

                def _ensure_endswith_period[S: str](value: S, name: str) -> S:
                    assert isinstance(value, str)
                    if not value.endswith("."):
                        logger.warning(
                            "RocqCursorProtocol: %s (%s): %s doesn't end with '.'",
                            fn.__name__,
                            name,
                            value,
                        )
                        return cast(S, f"{value}.")
                    return value

                # Process arguments if needed
                if argnames_set is not None:
                    bound_args = signature.bind(*args, **kwargs)
                    bound_args.apply_defaults()
                    for argname in argnames_set:
                        if argname in bound_args.arguments:
                            bound_args.arguments[argname] = _ensure_endswith_period(
                                bound_args.arguments[argname],
                                f"argument '{argname}'",
                            )
                    result = fn(*bound_args.args, **bound_args.kwargs)
                else:
                    result = fn(*args, **kwargs)

                # Process return value if needed
                if return_:
                    if isinstance(result, str):
                        result = _ensure_endswith_period(result, "return value")
                    else:
                        raise RuntimeError(
                            f"RocqCursorProtocol: {fn.__name__}: return value is not a string: {type(result)}"
                        )

                return result

            return _wrapped

        return decorator

    def advance_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]: ...

    def clear_suffix(self, count: int | None = None) -> None: ...

    def materialize(self) -> None:
        """Enable parallel processing on this cursor."""
        ...

    def clone(self, *, materialize: bool = False) -> RocqCursor: ...

    def commit(
        self,
        file: str | None,
        *,
        include_ghost: bool = False,
        include_suffix: bool = True,
    ) -> None | rdm_api.Err[None]: ...

    def compile(self) -> rdm_api.CompileResult: ...

    def cursor_index(self) -> int: ...

    def dispose(self) -> None: ...

    def doc_prefix(self) -> list[rdm_api.PrefixItem]: ...

    def doc_suffix(self) -> list[rdm_api.SuffixItem]: ...

    def go_to(self, index: int) -> None | rdm_api.Err[rdm_api.CommandError | None]: ...

    def has_suffix(self) -> bool: ...

    def insert_blanks(self, text: str) -> None: ...

    def _insert_command(
        self, text: str
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]: ...

    @ensure_endswith_period(argnames="text")
    def insert_command(
        self, text: str, blanks: str | None = "\n", safe: bool = True
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        if safe:
            prefix = self.doc_prefix()
            if prefix != [] and prefix[-1].kind != "blanks":
                self.insert_blanks(" ")
                revert = True
            else:
                revert = False
        else:
            revert = False

        try:
            result = self._insert_command(text)
            if isinstance(result, rdm_api.CommandError):
                if revert:
                    self.revert_before(erase=True, index=len(prefix))
            elif blanks is not None:
                self.insert_blanks(blanks)
            return result
        except rdm_api.Error:
            if revert:
                self.revert_before(erase=True, index=len(prefix))
            raise

    def load_file(
        self,
    ) -> None | rdm_api.Err[rdm_api.RocqLoc | None]: ...

    # TODO: we should really reduce the repetition on [query],
    # there are 5 functions, but they all do basically the same thing
    def query(self, text: str) -> rdm_api.CommandData | rdm_api.Err[None]: ...

    def query_json(self, text: str, *, index: int) -> Any | rdm_api.Err[None]: ...

    def query_json_all(
        self, text: str, *, indices: list[int] | None
    ) -> list[Any] | rdm_api.Err[None]: ...

    def query_text(self, text: str, *, index: int) -> str | rdm_api.Err[None]: ...

    def query_text_all(
        self, text: str, *, indices: list[int] | None
    ) -> list[str] | rdm_api.Err[None]: ...

    def revert_before(self, erase: bool, index: int) -> None | rdm_api.Err[None]: ...

    def run_command(self, text: str) -> rdm_api.CommandData | rdm_api.Err[None]: ...

    def run_step(
        self,
    ) -> rdm_api.CommandData | None | rdm_api.Err[rdm_api.CommandError]: ...

    def run_steps(self, count: int) -> None | rdm_api.Err[rdm_api.StepsError]: ...

    # ===== BEGIN: contextmanagers ============================================
    @contextmanager
    def ctx(self, rollback: bool = True) -> Iterator[Self]:
        """Base RDM context manager supporting optional doc rollback."""
        current_idx: int = 0  # satisfies pyright.
        if rollback:
            current_idx = self.cursor_index()
            # NOTE: blanks are fused, so inserting blanks at the beginning
            # of a rollback context can leave the document in a modified state.
            # By inserting a real (but trivial) command that we rollback, we
            # ensure that the document is left unchanged.
            marker_cmd = "Check tt."
            insert_command_reply = self.insert_command(marker_cmd)
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
            revert_reply = self.revert_before(True, current_idx)
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
    def aborted_goal_ctx(
        self, goal: str = "True", rollback: bool = True
    ) -> Iterator[Self]:
        """RDM context manager that sets up an aborted goal."""
        with self.ctx(rollback=rollback):
            goal_reply = self.insert_command(f"Goal {goal}.")
            if isinstance(goal_reply, rdm_api.Err):
                raise rdm_api.Error(goal_reply)

            yield self

            abort_reply = self.insert_command("Abort.")
            if isinstance(abort_reply, rdm_api.Err):
                raise rdm_api.Error(abort_reply)

    # NOTE: we could expose a more structured way to build the context list.
    @contextmanager
    def Section(
        self,
        name: str,
        context: list[str] | None = None,
        rollback: bool = False,
    ) -> Iterator[Self]:
        with self.ctx(rollback=rollback):
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
    def goto_first_match(
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
        prefix = self.doc_prefix()
        suffix = self.doc_suffix()

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

        def check_result(result: rdm_api.Err | object, mtch: tuple[int, str]) -> bool:
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
                run_step_reply = self.run_step()
                if isinstance(run_step_reply, rdm_api.Err):
                    logger.warning(
                        "Failed to step over the match: {run_step_repl}",
                    )
                    return False
            return True

        if include_prefix:
            if skip < len(candidate_prefix_matches):
                # Use this match
                return check_result(
                    self.go_to(candidate_prefix_matches[skip][0]),
                    candidate_prefix_matches[skip],
                )
            else:
                skip -= len(candidate_prefix_matches)

        if len(candidate_suffix_matches) <= skip:
            return False

        advance_to_reply = self.advance_to(candidate_suffix_matches[skip][0])
        return check_result(advance_to_reply, candidate_suffix_matches[skip])

    # ===== END: visitors =====================================================

    # ===== BEGIN: macros =====================================================
    def Compute(
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
        with self.aborted_goal_ctx(goal=f"exists v, v = ({term})", rollback=rollback):
            command_reply = self.insert_command("vm_compute.")
            if isinstance(command_reply, rdm_api.Err):
                return command_reply

            query_reply = self.query_text_all(
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

    def current_goal(self) -> rdm_api.ProofState | None:
        result = self.query("About nat.")
        assert not isinstance(result, rdm_api.Err)
        return result.proof_state

    def _import_export_cmd(
        self,
        kind: Literal["Import"] | Literal["Export"],
        logpath: str,
        require: bool = True,
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        cmd: str = f"{'Require ' if require else ''}{kind} {logpath}."
        return self.insert_command(cmd)

    def Import(
        self,
        logpath: str,
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return self._import_export_cmd("Import", logpath, require=False)

    def Export(
        self,
        logpath: str,
        require: bool = True,
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return self._import_export_cmd("Export", logpath, require=False)

    def RequireImport(
        self,
        logpath: str,
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return self._import_export_cmd("Import", logpath, require=True)

    def RequireExport(
        self,
        logpath: str,
        require: bool = True,
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return self._import_export_cmd("Export", logpath, require=True)

    def fresh_ident(self, ident: str) -> str | rdm_api.Err[None]:
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
        result = self.query_text(
            f'Eval lazy in ltac:(let nm := fresh "{ident}" in idtac nm).', index=0
        )
        if isinstance(result, rdm_api.Err):
            return rdm_api.Err("Not in proof mode", None)
        return result

    # ===== END: macros =======================================================

    # ===== BEGIN: contextmanagers ============================================
    @contextmanager
    def sess(self) -> Iterator[Self]:
        yield self
        self.dispose()

    # ===== END: contextmanagers ===============================================
