"""
Add structured logging (via observability) on top of the RocqCursor API.
"""

from __future__ import annotations

import functools
import hashlib
import inspect
from collections.abc import Awaitable, Callable, Coroutine
from types import CoroutineType
from typing import Any, override

from observability import (
    get_logger,
    model_as_otel_attrs,
    set_otel_attrs_on_span,
    trace_context,
)
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_doc_manager.cursor import DelegateRocqCursor

from .attrs import LocationInfo, TraceCursorSpanAttrs

logger = get_logger("RocqCursor")


async def _maybe_await[T](val: T | Awaitable[T]) -> T:
    if inspect.isawaitable(val):
        return await val
    return val


def _trace[**P, A, B, T](
    *,
    after: bool = False,
    method: str | None = None,
    cmd: Callable[[dict[str, Any]], str] | None = None,
    inputs: Callable[[TracingCursor, dict[str, Any]], Any] | None = None,
) -> Callable[[Callable[P, Coroutine[A, B, T]]], Callable[P, CoroutineType[A, B, T]]]:
    fn_input = (lambda _, args: args) if inputs is None else inputs

    def wrap(func: Callable):
        sig = inspect.signature(func)
        meth = f"RocqCursor.{method or func.__name__}"

        @functools.wraps(func)
        async def wrapper(self: TracingCursor, *args, **kwargs):
            bound_args = sig.bind(self, *args, **kwargs)
            bound_args.apply_defaults()
            args_dict = dict(bound_args.arguments)
            args_dict.pop("self", None)

            attrs = TraceCursorSpanAttrs.model_construct(
                args=await _maybe_await(fn_input(self, args_dict))
            )
            if cmd:
                attrs.action = await _maybe_await(cmd(args_dict))

            with trace_context(meth) as span:
                try:
                    attrs.before = LocationInfo(**await self.location_info())

                    result = await func(self, *args, **kwargs)

                    if result is not None:
                        attrs.error = isinstance(result, rdm_api.Err)
                        attrs.result_type = str(type(result))
                        attrs.result = result

                    if after:
                        attrs.after = LocationInfo(**await self.location_info())

                    return result
                finally:
                    logger.info(meth, **attrs.model_dump(exclude_none=True))
                    set_otel_attrs_on_span(
                        span, model_as_otel_attrs(attrs, prefix=meth)
                    )

        return wrapper

    return wrap


class TracingCursor(DelegateRocqCursor):
    """
    An implementation of the rdm_api.API that traces all document interactions recording
    a state_id.
    """

    @staticmethod
    def of_cursor(rc: RocqCursor, *, verbose: bool = False) -> TracingCursor:
        return TracingCursor(rc, verbose=verbose)

    def __init__(self, rc: RocqCursor, *, verbose: bool = True) -> None:
        super().__init__(rc)
        self._verbose = verbose

    @override
    def make_derived(self, rc: RocqCursor) -> RocqCursor:
        return TracingCursor.of_cursor(rc, verbose=self._verbose)

    @override
    @_trace(
        method="insert_command",
        after=True,
    )
    async def _insert_command(
        self, text: str, *, ghost: bool = False
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return await self._cursor._insert_command(text, ghost=ghost)

    @staticmethod
    async def _next_command(me: TracingCursor, args: dict[str, Any]) -> dict[str, Any]:
        suffix = [item.text for item in await me.doc_suffix() if item.kind == "command"]
        return {"next_command": suffix[0] if suffix else None}

    @override
    @_trace(after=True, inputs=_next_command)
    async def run_step(
        self,
    ) -> rdm_api.CommandData | None | rdm_api.Err[rdm_api.CommandError]:
        return await self._cursor.run_step()

    @override
    @_trace()
    async def query(self, text: str) -> rdm_api.CommandData | rdm_api.Err[None]:
        return await self._cursor.query(text)

    @override
    @_trace()
    async def query_json(
        self, text: str, *, index: int
    ) -> Any | rdm_api.Err[rdm_api.CommandError]:
        return await self._cursor.query_json(text, index=index)

    @override
    @_trace()
    async def query_json_all(
        self, text: str, *, indices: list[int] | None = None
    ) -> list[Any] | rdm_api.Err[None]:
        return await self._cursor.query_json_all(text, indices=indices)

    @override
    @_trace()
    async def query_text(self, text: str, *, index: int) -> str | rdm_api.Err[None]:
        return await self._cursor.query_text(text, index=index)

    @override
    @_trace()
    async def query_text_all(
        self, text: str, *, indices: list[int] | None = None
    ) -> list[str] | rdm_api.Err[None]:
        return await self._cursor.query_text_all(text, indices=indices)

    # NAVIGATION
    @override
    @_trace(after=True)
    async def revert_before(self, erase: bool, index: int) -> None | rdm_api.Err[None]:
        return await self._cursor.revert_before(erase, index)

    @override
    @_trace(after=True)
    async def advance_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        # TODO: it might be necessary to insert all of the commands here
        return await self._cursor.advance_to(index=index)

    @override
    @_trace(after=True)
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
        # -[via _trace]->         TracingCursor.location_info
        # ------------------>     TracingCursor.current_goal ~= RocqCursor.current_goal
        # -[via self.query]->     TracingCursor.query
        result = await self._cursor.query("About nat.")
        assert not isinstance(result, rdm_api.Err)
        return result.proof_state

    async def run_steps(self, count: int) -> None | rdm_api.Err[rdm_api.StepsError]:
        for cnt in range(count):
            result = await self.run_step()
            if isinstance(result, rdm_api.Err):
                return rdm_api.Err(
                    message=result.message,
                    data=rdm_api.StepsError(cmd_error=result.data, nb_processed=cnt),
                )
        return None
