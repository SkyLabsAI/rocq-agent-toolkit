"""
Add structured logging (via observability) on top of the RocqCursor API.
"""

from __future__ import annotations

import functools
import hashlib
import inspect
from collections.abc import Awaitable, Callable, Coroutine
from copy import deepcopy
from types import CoroutineType, FunctionType
from typing import Any, Final, Literal, get_protocol_members, override

import rocq_agent_toolkit_utils as rat_utils
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


async def _maybe_next_action(
    rc: RocqCursor, args: dict[str, Any]
) -> tuple[str, Literal["blanks", "command", "ghost"]] | None:
    if suffix := await rc.doc_suffix():
        return (suffix[0].text, suffix[0].kind)
    else:
        return None


def _trace_targets(
    *,
    cls: type[RocqCursor] = RocqCursor,
    skip: set[str],
    trace_kwargs: dict[str, dict[str, Any]],
) -> dict[str, dict[str, Any]]:
    assert not (skip & set(trace_kwargs.keys())), (
        f"skip should not overlap with trace_kwargs:{rat_utils.objects.info(skip, trace_kwargs)}"
    )
    assert set(get_protocol_members(RocqCursor)) <= set(dir(cls)), (
        f"{cls.__qualname__} must derive from RocqCursor:{rat_utils.objects.info(cls)}",
    )

    targets: dict[str, dict[str, Any]] = {}
    for target_nm in (
        {
            attr_nm
            for attr_nm in get_protocol_members(RocqCursor)
            if callable(getattr(RocqCursor, attr_nm))
        }
        | trace_kwargs.keys()
    ) - skip:
        assert hasattr(cls, target_nm), f"{cls.__qualname__} missing {target_nm}"
        target_fn = getattr(cls, target_nm)
        assert callable(target_fn), (
            f"{cls.__qualname__}.{target_nm} is not Callable: {repr(target_fn)}"
        )
        assert isinstance(target_fn, FunctionType), (
            f"{cls.__qualname__}.{target_nm} should be a function: {repr(target_fn)}"
        )

        if target_nm in trace_kwargs:
            targets[target_nm] = deepcopy(trace_kwargs[target_nm])
        else:
            targets[target_nm] = {}

    return targets


# methods that should not be instrumented with _trace
_TRACING_CURSOR_DEFAULT_SKIP: Final[set[str]] = {
    "_import_export_cmd",
    "_untraced_location_info",
    "_untraced_doc_prefix",
    "_untraced_current_goal",
}
# custom kwargs to use for _trace; default=dict()
_TRACING_CURSOR_DEFAULT_TRACE_KWARGS: Final[dict[str, dict[str, Any]]] = {
    "advance_to": {
        "effect": True,
    },
    "clear_suffix": {
        "effect": True,
    },
    "go_to": {
        "effect": True,
    },
    "insert_blanks": {
        "effect": lambda _, args: (args["text"], "blanks"),
    },
    "_insert_command": {
        "method": "insert_command",
        "effect": lambda _, args: (
            args["text"],
            "ghost" if args["ghost"] else "command",
        ),
    },
    "insert_command": {
        "method": "insert_command_pad_blanks",
        "effect": True,
    },
    "insert_sentences": {
        "effect": True,
    },
    "revert_before": {
        "effect": True,
    },
    "run_command": {"effect": lambda _, args: (args["text"], "ghost")},
    "run_step": {
        "effect": _maybe_next_action,
    },
    "run_steps": {
        "effect": lambda _, args: 0 < args["count"],
        "partial_effect": True,
    },
    "ctx": {
        "effect": lambda _, args: not args["rollback"],
    },
    "aborted_goal_ctx": {
        "effect": lambda _, args: not args["rollback"],
    },
    "Section": {
        "effect": lambda _, args: not args["rollback"],
    },
    "goto_first_match": {
        "effect": True,
    },
    "Compute": {
        "effect": lambda _, args: not args["rollback"],
    },
    "Import": {
        "effect": True,
    },
    "RequireImport": {
        "effect": True,
    },
    "Export": {
        "effect": True,
    },
    "RequireExport": {
        "effect": True,
    },
}
assert _trace_targets(
    # additionally skip the custom methods on DelegateRocqCursor+TracingCursor
    skip=_TRACING_CURSOR_DEFAULT_SKIP,
    trace_kwargs=_TRACING_CURSOR_DEFAULT_TRACE_KWARGS,
).keys() <= set(get_protocol_members(RocqCursor)), (
    "Default trace candidates must be a subset of RocqCursor methods"
)


def _trace_method[**P, A, B, T](
    *,
    method: str | None = None,
    effect: (
        Callable[
            [TracingCursor, dict[str, Any]],
            Awaitable[tuple[str, Literal["blanks", "command", "ghost"]] | bool | None],
        ]
        | Callable[
            [TracingCursor, dict[str, Any]],
            tuple[str, Literal["blanks", "command", "ghost"]] | bool | None,
        ]
        | bool
        | None
    ) = None,
    partial_effect: bool = False,
) -> Callable[[Callable[P, Coroutine[A, B, T]]], Callable[P, CoroutineType[A, B, T]]]:
    """Decorator: use an opentelemetry to instrument a TracingCursor method.

    Arguments:
        method (optional): name to use instead of the method name
        effect (optional): characterize the effect & control whether after_id is generated (use most specific):
            - Callable: use self+args_dict to produce either:
              - the text+kind for a /single/ document interaction
              - a boolean indicating whether there was an effect
            - bool: whether a document effect was produced (either via navigation or a composite interaction)
            - None (default): no document interaction
        partial_effect (optional): whether partial effects remain if rdm_api.Err is returned
    Returns:
        instrumented method
    """

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
                args={
                    k: v
                    for k, v in args_dict.items()
                    if not isinstance(v, TracingCursor)
                }
            )
            need_after_id: bool = False

            if effect is not None:
                if isinstance(effect, bool):
                    need_after_id = effect
                else:
                    effect_result = await _maybe_await(effect(self, args_dict))
                    if isinstance(effect_result, bool):
                        need_after_id = effect_result
                    elif isinstance(effect_result, tuple):
                        assert len(effect_result) == 2, (
                            f"effect callbacks for _trace should produce 2-tuples: {effect_result}"
                        )
                        text, kind = effect_result
                        need_after_id = kind != "ghost"
                        attrs.action = text
                        attrs.action_kind = kind

            with trace_context(meth) as span:
                try:
                    attrs.before = LocationInfo(**await self._untraced_location_info())

                    result = await func(self, *args, **kwargs)

                    if result is not None:
                        attrs.error = isinstance(result, rdm_api.Err)
                        attrs.result_type = str(type(result))
                        if not isinstance(result, TracingCursor):
                            attrs.result = result

                    if (not attrs.error or partial_effect) and need_after_id:
                        attrs.after = LocationInfo(
                            **await self._untraced_location_info()
                        )

                    return result
                finally:
                    logger.info(meth, **attrs.model_dump(exclude_none=True))
                    set_otel_attrs_on_span(
                        span, model_as_otel_attrs(attrs, prefix=meth)
                    )

        return wrapper

    return wrap


def _trace_cls(
    *,
    extra_skip: set[str] | None = None,
    extra_trace_kwargs: dict[str, dict[str, Any]] | None = None,
) -> Callable[[type[DelegateRocqCursor]], type[DelegateRocqCursor]]:
    """Decorator: auto-instrument a DelegateRocqCursor deriver."""

    def wrap(cls: type[DelegateRocqCursor]) -> type[DelegateRocqCursor]:
        skip = deepcopy(_TRACING_CURSOR_DEFAULT_SKIP)
        skip |= set() if extra_skip is None else extra_skip

        trace_kwargs = deepcopy(_TRACING_CURSOR_DEFAULT_TRACE_KWARGS)
        trace_kwargs.update({} if extra_trace_kwargs is None else extra_trace_kwargs)

        for fn_nm, fn_trace_kwargs in _trace_targets(
            cls=cls, skip=skip, trace_kwargs=trace_kwargs
        ).items():
            assert hasattr(cls, fn_nm), "ensured by _trace_targets"
            fn = getattr(cls, fn_nm)
            assert callable(fn), "ensured by _trace_targets"
            assert isinstance(fn, FunctionType), "ensured by _trace_targets"

            setattr(cls, fn_nm, override(_trace_method(**fn_trace_kwargs)(fn)))

        return cls

    return wrap


@_trace_cls()
class TracingCursor(DelegateRocqCursor):
    """
    An implementation of the rdm_api.API that traces all document interactions recording
    a state_id.
    """

    def __init__(self, rc: RocqCursor, *, verbose: bool = True) -> None:
        super().__init__(rc)
        self._verbose = verbose

    @staticmethod
    def of_cursor(rc: RocqCursor, *, verbose: bool = False) -> TracingCursor:
        return TracingCursor(rc, verbose=verbose)

    @override
    def make_derived(self, rc: RocqCursor) -> RocqCursor:
        return TracingCursor.of_cursor(rc, verbose=self._verbose)

    async def _untraced_location_info(self) -> dict[str, Any]:
        """Construct a functional location by computing the hash of the effectful commands."""
        prefix = await self._untraced_doc_prefix()
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

    async def _untraced_doc_prefix(self) -> list[rdm_api.PrefixItem]:
        return await self._cursor.doc_prefix()

    async def _untraced_current_goal(self) -> rdm_api.ProofState | None:
        # Avoid cycle leading to unbounded recursion & stack overflow:
        #                         TracingCursor.query
        # -[via _trace]->         TracingCursor.location_info
        # ------------------>     TracingCursor.current_goal ~= RocqCursor.current_goal
        # -[via self.query]->     TracingCursor.query
        result = await self._cursor.query("About nat.")
        assert not isinstance(result, rdm_api.Err)
        return result.proof_state
