from __future__ import annotations

import functools
import hashlib
import inspect
from collections.abc import Awaitable, Callable, Coroutine
from types import CoroutineType
from typing import Any, override

from observability import get_logger
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

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


async def _maybe_await[T](val: T | Awaitable[T]) -> T:
    if inspect.isawaitable(val):
        return await val
    return val


def _trace_log[**P, A, B, T](
    *,
    after: bool = False,
    method: str | None = None,
    cmd: Callable[[dict[str, Any]], str] | None = None,
    inputs: Callable[[TracingCursor, dict[str, Any]], Any] | None = None,
    output: Callable[[Any], Any] | None = None,
    exception: Callable[[Any], Any] | None = None,
) -> Callable[[Callable[P, Coroutine[A, B, T]]], Callable[P, CoroutineType[A, B, T]]]:
    fn_input = (lambda _, args: args) if inputs is None else inputs
    fn_output = _default_fn if output is None else output
    fn_except = _default_fn if exception is None else exception

    def wrap(func: Callable):
        sig = inspect.signature(func)
        meth = method or func.__name__

        @functools.wraps(func)
        async def wrapper(self: TracingCursor, *args, **kwargs):
            # Bind arguments to the function signature
            bound_args = sig.bind(self, *args, **kwargs)
            bound_args.apply_defaults()
            # Convert to dict
            args_dict = dict(bound_args.arguments)

            # it is important that we get the location before we run the function
            before_loc = await self.location_info()
            log_args: dict[str, Any] = {"before": before_loc}
            log_args["args"] = await _maybe_await(fn_input(self, args_dict))
            if cmd:
                log_args["action"] = await _maybe_await(cmd(args_dict))
            try:
                result = await _maybe_await(func(self, *args, **kwargs))
                log_args["result"] = fn_output(result)
                if result is not None:
                    log_args["result_type"] = str(type(result))
                    log_args["error"] = isinstance(result, rdm_api.Err)
                if after:
                    after_loc = await self.location_info()
                    log_args["after"] = after_loc
                    before_idx = before_loc.get("index")
                    after_idx = after_loc.get("index")
                    if isinstance(before_idx, int) and isinstance(after_idx, int):
                        delta = after_idx - before_idx
                        log_args["delta"] = delta
                logger.info(f"RocqCursor.{meth}", **log_args)
                return result
            except Exception as err:
                log_args["exception"] = fn_except(err)
                logger.info(f"RocqCursor.{meth}", **log_args)
                raise

        return wrapper

    return wrap


class TracingCursor(RocqCursor):
    """
    An implementation of the rdm_api.API that traces all document interactions recording
    a state_id.
    """

    @staticmethod
    def of_cursor(rc: RocqCursor, *, verbose: bool = False) -> TracingCursor:
        return TracingCursor(rc, verbose=verbose)

    def __init__(self, rc: RocqCursor, *, verbose: bool = True) -> None:
        self._cursor = rc
        self._verbose = verbose

    @override
    async def clone(self, *, materialize: bool = False) -> RocqCursor:
        # We don't trace this because we don't care about the cursor, but
        # we do care that the result is also traced in the same way
        cloned = await self._cursor.clone(materialize=materialize)
        return TracingCursor(cloned, verbose=self._verbose)

    @override
    @_trace_log(
        method="insert_command",
        after=True,
        inputs=lambda _, args: (args["text"], args["ghost"]),
    )
    async def _insert_command(
        self, text: str, *, ghost: bool = False
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return await self._cursor._insert_command(text, ghost=ghost)

    @staticmethod
    async def _next_command(me: TracingCursor, args: dict[str, Any]) -> str | None:
        suffix = [item.text for item in await me.doc_suffix() if item.kind == "command"]
        return suffix[0] if suffix else None

    @override
    @_trace_log(after=True, inputs=_next_command)
    async def run_step(
        self,
    ) -> rdm_api.CommandData | None | rdm_api.Err[rdm_api.CommandError]:
        return await self._cursor.run_step()

    @override
    @_trace_log(inputs=lambda _, args: args["text"])
    async def query(self, text: str) -> rdm_api.CommandData | rdm_api.Err[None]:
        return await self._cursor.query(text)

    @override
    @_trace_log(inputs=lambda _, args: args)
    async def query_json(
        self, text: str, *, index: int
    ) -> Any | rdm_api.Err[rdm_api.CommandError]:
        return await self._cursor.query_json(text, index=index)

    @override
    @_trace_log(inputs=lambda _, args: args["text"])
    async def query_json_all(
        self, text: str, *, indices: list[int] | None = None
    ) -> list[Any] | rdm_api.Err[None]:
        return await self._cursor.query_json_all(text, indices=indices)

    @override
    @_trace_log(inputs=lambda _, args: args)
    async def query_text(self, text: str, *, index: int) -> str | rdm_api.Err[None]:
        return await self._cursor.query_text(text, index=index)

    @override
    @_trace_log(inputs=lambda _, args: args["text"])
    async def query_text_all(
        self, text: str, *, indices: list[int] | None = None
    ) -> list[str] | rdm_api.Err[None]:
        return await self._cursor.query_text_all(text, indices=indices)

    # NAVIGATION
    @override
    @_trace_log(inputs=lambda _, args: args, after=True)
    async def revert_before(self, erase: bool, index: int) -> None | rdm_api.Err[None]:
        return await self._cursor.revert_before(erase, index)

    @override
    @_trace_log(inputs=lambda _, args: args, after=True)
    async def advance_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        # TODO: it might be necessary to insert all of the commands here
        return await self._cursor.advance_to(index=index)

    @override
    @_trace_log(inputs=lambda _, args: args, after=True)
    async def go_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        return await self._cursor.go_to(index)

    async def location_info(self) -> dict[str, Any]:
        """Construct a functional location by computing the hash of the effectful commands."""
        prefix = await self.doc_prefix()
        raw = "\n".join(
            [
                elem.text
                for elem in prefix
                if elem.kind == "command" or elem.kind == "ghost"
            ]
        )
        result = {"id": hashlib.md5(raw.encode("utf-8")).hexdigest()}
        if self._verbose and (goal := await self._untraced_current_goal()):
            result["goal"] = goal.model_dump_json()
        return result

    async def _untraced_current_goal(self) -> rdm_api.ProofState | None:
        # Avoid cycle leading to unbounded recursion & stack overflow:
        #                         TracingCursor.query
        # -[via _trace_log]->     TracingCursor.location_info
        # ------------------>     TracingCursor.current_goal ~= RocqCursor.current_goal
        # -[via self.query]->     TracingCursor.query
        result = await self._cursor.query("About nat.")
        assert not isinstance(result, rdm_api.Err)
        return result.proof_state

    async def doc_prefix(self) -> list[rdm_api.PrefixItem]:
        return await self._cursor.doc_prefix()

    async def doc_suffix(self) -> list[rdm_api.SuffixItem]:
        return await self._cursor.doc_suffix()

    async def clear_suffix(self, count: int | None = None) -> None:
        return await self._cursor.clear_suffix(count)

    async def commit(
        self,
        file: str | None,
        *,
        include_ghost: bool = False,
        include_suffix: bool = True,
    ) -> None | rdm_api.Err[None]:
        return await self._cursor.commit(
            file, include_ghost=include_ghost, include_suffix=include_suffix
        )

    async def run_steps(self, count: int) -> None | rdm_api.Err[rdm_api.StepsError]:
        for cnt in range(count):
            result = await self.run_step()
            if isinstance(result, rdm_api.Err):
                return rdm_api.Err(
                    message=result.message,
                    data=rdm_api.StepsError(cmd_error=result.data, nb_processed=cnt),
                )
        return None

    async def compile(self) -> rdm_api.CompileResult:
        return await self._cursor.compile()

    async def materialize(self) -> None:
        return await self._cursor.materialize()

    async def cursor_index(self) -> int:
        return await self._cursor.cursor_index()

    async def dispose(self) -> None:
        return await self._cursor.dispose()

    async def has_suffix(self) -> bool:
        return await self._cursor.has_suffix()

    async def insert_blanks(self, text: str) -> None:
        return await self._cursor.insert_blanks(text)

    async def load_file(self) -> None | rdm_api.Err[rdm_api.RocqLoc | None]:
        return await self._cursor.load_file()
