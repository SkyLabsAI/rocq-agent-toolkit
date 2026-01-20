from __future__ import annotations

import functools
import hashlib
import inspect
from collections.abc import Callable
from typing import Any, override

from observability import get_logger
from rocq_doc_manager import RocqCursor
from rocq_doc_manager.rocq_doc_manager_api import RocqDocManagerAPI

logger = get_logger("RocqCursor")


def _default_fn(x: Any) -> Any:
    if hasattr(x, "to_json"):
        return x.to_json()
    elif isinstance(x, list):
        return [_default_fn(x) for x in x]
    elif isinstance(x, dict):
        return {str(k): _default_fn(v) for k, v in x.items()}
    elif isinstance(x, str):
        return x
    elif isinstance(x, int):
        return x
    elif isinstance(x, float):
        return x
    return x


def _trace_log(
    *,
    after: bool = False,
    cmd: Callable[[dict[str, Any]], str] | None = None,
    inputs: Callable[[RocqCursor, dict[str, Any]], Any] | None = None,
    output: Callable[[Any], Any] | None = None,
    exception: Callable[[Any], Any] | None = None,
):
    fn_input = (lambda _, args: args) if inputs is None else inputs
    fn_output = _default_fn if output is None else output
    fn_except = _default_fn if exception is None else exception

    def wrap(func: Callable):
        sig = inspect.signature(func)

        @functools.wraps(func)
        def wrapper(self: TracingCursor, *args, **kwargs):
            # Bind arguments to the function signature
            bound_args = sig.bind(self, *args, **kwargs)
            bound_args.apply_defaults()
            # Convert to dict
            args_dict = dict(bound_args.arguments)

            # it is important that we get the location before we run the function
            log_args: dict[str, Any] = {"before": self.location_info()}
            log_args["args"] = fn_input(self, args_dict)
            if cmd:
                log_args["action"] = cmd(args_dict)
            try:
                result = func(self, *args, **kwargs)
                log_args["result"] = fn_output(result)
                if after:
                    log_args["after"] = self.location_info()
                logger.info(f"RocqCursor.{func.__name__}", **log_args)
                return result
            except Exception as err:
                log_args["exception"] = fn_except(err)
                logger.info(f"RocqCursor.{func.__name__}", **log_args)
                raise

        return wrapper

    return wrap


class TracingCursor(RocqCursor):
    """
    An implementation of the RocqCursor API that traces all document interactions recording
    a state_id.
    """

    @staticmethod
    def of_cursor(rc: RocqCursor, *, verbose: bool = False) -> TracingCursor:
        assert rc._the_rdm is not None
        return TracingCursor(rc._the_rdm, rc._cursor, verbose=verbose)

    def __init__(
        self, rdm: RocqDocManagerAPI, cursor: int, *, verbose: bool = True
    ) -> None:
        super().__init__(rdm, cursor)
        self._verbose = verbose

    @override
    def clone(self, *, materialize: bool = False):
        # We don't trace this because we don't care about the cursor, but
        # we do care that the result is also traced in the same way
        result = super().clone(materialize=materialize)
        assert result._the_rdm is not None
        return TracingCursor(result._the_rdm, result._cursor, verbose=self._verbose)

    @override
    @_trace_log(after=True, inputs=lambda _, args: args["text"])
    def insert_command(
        self, text: str, blanks: str | None = "\n", safe: bool = True
    ) -> RocqCursor.CommandData | RocqCursor.Err[RocqCursor.CommandError]:
        return super().insert_command(text, blanks, safe)

    @override
    @_trace_log(after=True, inputs=lambda _, args: args["text"])
    def run_command(self, text: str) -> RocqCursor.CommandData | RocqCursor.Err[None]:
        return super().run_command(text)

    @staticmethod
    def _next_command(me: RocqCursor, args: dict[str, Any]) -> str | None:
        suffix = [item.text for item in me.doc_suffix() if item.kind == "command"]
        return suffix[0] if suffix else None

    @override
    @_trace_log(after=True, inputs=_next_command)
    def run_step(
        self,
    ) -> RocqCursor.CommandData | None | RocqCursor.Err[RocqCursor.CommandError | None]:
        return super().run_step()

    @override
    @_trace_log(inputs=lambda _, args: args["text"])
    def query(self, text: str) -> RocqCursor.CommandData | RocqCursor.Err[None]:
        return super().query(text)

    @override
    @_trace_log(inputs=lambda _, args: args)
    def query_json(
        self, text: str, *, index: int
    ) -> Any | RocqCursor.Err[RocqCursor.CommandError]:
        return super().query_json(text, index=index)

    @override
    @_trace_log(inputs=lambda _, args: args["text"])
    def query_json_all(
        self, text: str, *, indices: list[int] | None = None
    ) -> list[Any] | RocqCursor.Err[None]:
        return super().query_json_all(text, indices=indices)

    @override
    @_trace_log(inputs=lambda _, args: args)
    def query_text(self, text: str, *, index: int) -> str | RocqCursor.Err[None]:
        return super().query_text(text, index=index)

    @override
    @_trace_log(inputs=lambda _, args: args["text"])
    def query_text_all(
        self, text: str, *, indices: list[int] | None = None
    ) -> list[str] | RocqCursor.Err[None]:
        return super().query_text_all(text, indices=indices)

    # NAVIGATION
    @override
    @_trace_log(inputs=lambda _, args: args, after=True)
    def revert_before(self, erase: bool, index: int) -> None:
        return super().revert_before(erase, index)

    @override
    @_trace_log(inputs=lambda _, args: args, after=True)
    def advance_to(self, index: int) -> None:
        # TODO: it might be necessary to insert all of the commands here
        super().advance_to(index=index)

    @override
    @_trace_log(inputs=lambda _, args: args, after=True)
    def go_to(
        self, index: int
    ) -> None | RocqCursor.Err[RocqCursor.CommandError | None]:
        return super().go_to(index)

    def location_info(self) -> dict[str, Any]:
        """Construct a functional location by computing the hash of the effectful commands."""
        raw = "\n".join(
            [
                elem.text
                for elem in self.doc_prefix()
                if elem.kind == "command" or elem.kind == "ghost"
            ]
        )
        result = {"id": hashlib.md5(raw.encode("utf-8")).hexdigest()}
        if self._verbose and (goal := self._untraced_current_goal()):
            result["goal"] = goal.to_json()
        return result

    def _untraced_current_goal(self) -> RocqCursor.ProofState | None:
        # Avoid cycle leading to unbounded recursion & stack overflow:
        #                         TracingCursor.query
        # -[via _trace_log]->     TracingCursor.location_info
        # ------------------>     TracingCursor.current_goal ~= RocqCursor.current_goal
        # -[via self.query]->     TracingCursor.query
        result = super().query("About nat.")
        assert not isinstance(result, RocqCursor.Err)
        return result.proof_state
