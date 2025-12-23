from __future__ import annotations

import functools
import inspect
import logging
from abc import ABC, abstractmethod
from collections.abc import Callable, Collection
from typing import Any, TypeAlias, get_type_hints, overload

from jsonrpc_tp import JsonRPCTP

from .rocq_doc_manager_api import RocqDocManagerAPI

logger = logging.getLogger(__name__)


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

    @staticmethod
    def ensure_text_endswith_period[**P, T](fn: Callable[P, T]) -> Callable[P, T]:
        """Decorator (common case): ensure that the "text" argument ends with a period."""
        return RocqCursorProtocol.ensure_args_endswith_period(fn)

    @overload
    @staticmethod
    def ensure_args_endswith_period[**P, T](
        maybe_fn: Callable[P, T],
        *,
        argnames: Collection[str] | str,
    ) -> Callable[P, T]:
        """Decorator overload: narrow type when `maybe_fn` is not `None`."""

    @overload
    @staticmethod
    def ensure_args_endswith_period[**P, T](
        maybe_fn: None = None,
        *,
        argnames: Collection[str] | str,
    ) -> Callable[[Callable[P, T]], Callable[P, T]]:
        """Decorator overload: narrow type when `maybe_fn` is `None`."""

    # TODO: simplify this+overloads with use of `wrapt` once opentelemetry-python-contrib
    # relaxes too-strict version constraints.
    #
    # cf. https://github.com/open-telemetry/opentelemetry-python-contrib/pull/3930
    @staticmethod
    def ensure_args_endswith_period[**P, T](
        maybe_fn: Callable[P, T] | None = None,
        *,
        argnames: Collection[str] | str = "text",
    ) -> Callable[P, T] | Callable[[Callable[P, T]], Callable[P, T]]:
        """Decorator: ensure that named arguments (in args or kwargs) end with period.

        If a named argument doesn't end with a period, emit a `logger.warning`.

        Args:
            maybe_fn: The function to decorate, or None if used as @decorator()
            argnames: Collection of argument names to check, or a single string.
                     If None, defaults to ["text"].
                     If a string, converted to [string].

        Examples:
            @ensure_args_endswith_period  # defaults to ["text"]
            @ensure_args_endswith_period("text")  # single string
            @ensure_args_endswith_period(["text"])  # list
            @ensure_args_endswith_period(["text1", "text2"])  # multiple
        """
        if isinstance(argnames, str):
            argnames = {argnames}
        else:
            argnames = set(argnames)

        if not argnames:
            raise ValueError(
                "RocqCursorProtocol.ensure_args_endswith_period: argnames empty"
            )

        @functools.cache
        def _validated_signature(fn: Callable[P, T]) -> inspect.Signature:
            signature = inspect.signature(fn)
            # Validate that all requested argnames were found
            fn_argnames = signature.parameters.keys()
            missing_argnames = argnames - fn_argnames
            if missing_argnames:
                raise ValueError(
                    f"{missing_argnames} not found in parameters of "
                    f"{fn.__name__}: {signature}"
                )

            for argname in argnames:
                param = signature.parameters[argname]
                if (
                    param.annotation is not None
                    and param.annotation is not inspect.Parameter.empty
                ):
                    # Resolve string annotations (from __future__ import annotations)
                    # Try to get resolved type hints, fallback to annotation if it fails
                    try:
                        type_hints = get_type_hints(fn, include_extras=False)
                        resolved_annotation = type_hints.get(argname, param.annotation)
                    except Exception:
                        # If get_type_hints fails, use the annotation as-is
                        resolved_annotation = param.annotation

                    # Check if annotation is str type (handle both str type and "str" string)
                    if resolved_annotation != str and resolved_annotation != "str":
                        raise ValueError(
                            f"parameter {argname} of {fn.__name__} "
                            f"should be str: {resolved_annotation}"
                        )

            return signature

        def decorator(fn: Callable[P, T]) -> Callable[P, T]:
            signature = _validated_signature(fn)

            @functools.wraps(fn)
            def _wrapped(*args: P.args, **kwargs: P.kwargs) -> T:
                def _ensure_rocq_cmd_endswith_period(argname: str, cmd: str) -> str:
                    if not cmd.endswith("."):
                        logger.warning(
                            "RocqCursorProtocol: %s: argument '%s' doesn't end with '.'",
                            fn.__name__,
                            argname,
                        )
                        cmd += "."
                    return cmd

                bound_args = signature.bind(*args, **kwargs)
                for argname in argnames:
                    if argname in bound_args.arguments:
                        bound_args.arguments[argname] = (
                            _ensure_rocq_cmd_endswith_period(
                                argname,
                                bound_args.arguments[argname],
                            )
                        )

                return fn(*bound_args.args, **bound_args.kwargs)

            return _wrapped

        # Note: allow the decorator to work both:
        # - without any args/parens (default: argnames="text"):
        #   + `@RocqCursorProtocol.ensure_args_endswith_period`
        # - with parens or explicit argname overrides:
        #   + `@RocqCursorProtocol.ensure_args_endswith_period()`
        #   + `@RocqCursorProtocol.ensure_args_endswith_period("text")`
        #   + `@RocqCursorProtocol.ensure_args_endswith_period(["text1", "text2"])`
        #   + `@RocqCursorProtocol.ensure_args_endswith_period({"text1", "text2"})`
        return decorator if maybe_fn is None else decorator(maybe_fn)

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
    def copy_contents(self, dest: RocqCursorProtocol) -> None: ...

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
