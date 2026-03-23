"""Auto-instrumentation of `RocqCursor`s using (lexically scoped) span-based telemetry.

This module defines `InstrumentRocqCursor`, supporting configurable & extensible auto-instrumentation.

Instrumented methods generate an (opentelemetry) span with attributes matching the
`InstrumentRocqCursorSpanAttrs` schema (cf. `./schema.py`).

Auto-instrumentation is controlled -- using reasonable defaults -- via:
- `skip_auto_instrumentation_value`: predicate controlling which values are serialized as span attributes
- `skip_auto_instrumentation`: set of method names which should be skipped
- `custom_instrumentation_kwargs`: map from method names to custom instrumentation kwargs

Derivers that wish to customize the behavior should override the above methods & ensure that `super().XXX`
is called appropriately.

Note: in the future we could expose instrumentation decorators.
"""

from __future__ import annotations

import functools
import hashlib
import inspect
from collections.abc import Awaitable, Callable, Coroutine
from types import CoroutineType, FunctionType
from typing import Any, Concatenate, Literal, Self, get_protocol_members, override

from observability import (
    get_logger,
    model_as_otel_attrs,
    set_otel_attrs_on_span,
    trace_context,
)
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_doc_manager.cursor import DelegateRocqCursor

from .schema import InstrumentRocqCursorSpanAttrs, LocationInfo

logger = get_logger("RocqCursor")


async def _maybe_await[T](val: T | Awaitable[T]) -> T:
    if inspect.isawaitable(val):
        return await val
    return val


class InstrumentRocqCursor(DelegateRocqCursor):
    def __init_subclass__(cls) -> None:
        super().__init_subclass__()
        cls._auto_instrument()

    def __init__(self, rc: RocqCursor, *, verbose: bool = True) -> None:
        super().__init__(rc)
        self._verbose = verbose

    @classmethod
    def auto_instrument_skip_value(cls, v: Any) -> bool:
        return isinstance(v, InstrumentRocqCursor) or type(v) is type or callable(v)

    @classmethod
    def auto_instrument_skip(cls) -> set[str]:
        """Methods that should not be automatically instrumented."""
        return {
            # require manual instrumentation
            "load_file",
            "clone",
            # helper that introduces noise in telemetry data
            "_import_export_cmd",
            # internal helpers used to implement `instrument`
            "_untraced_location_info",
            "_untraced_current_goal",
        }

    @classmethod
    def custom_instrument_kwargs(cls) -> dict[str, dict[str, Any]]:
        """Custom instrumentation kwargs to use for methods; default=dict()."""
        return {
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
                "effect": lambda _, args: (
                    args["text"],
                    "ghost" if args["ghost"] else "command",
                ),
            },
            "insert_command": {
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
                "effect": cls._untraced_maybe_next_action,
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

    @classmethod
    def of_cursor(cls, rc: RocqCursor, *, verbose: bool = False) -> Self:
        if type(rc) is cls:
            return rc
        else:
            return cls(rc, verbose=verbose)

    @override
    def make_derived(self, rc: RocqCursor) -> Self:
        return self.of_cursor(rc, verbose=self._verbose)

    @override
    async def clone(self, *, materialize: bool = False) -> Self:
        return self.of_cursor(
            await self._cursor.clone(materialize=materialize), verbose=self._verbose
        )

    @override
    async def load_file(self) -> None | rdm_api.Err[rdm_api.RocqLoc | None]:
        # Note: we hand-trace `load_file` since instrument_method relies on
        # the document being loaded.
        meth = "RocqCursor.load_file"
        attrs = InstrumentRocqCursorSpanAttrs.model_construct()

        with trace_context(meth) as span:
            try:
                attrs.result = await self._cursor.load_file()

                if isinstance(attrs.result, rdm_api.Err):
                    attrs.error = True
                    attrs.result_type = "rdm_api.Err"
                else:
                    attrs.error = False
                    attrs.result_type = "None"
                    attrs.after = LocationInfo(**await self._untraced_location_info())

                return attrs.result
            except rdm_api.Error:
                attrs.error = True
                raise
            finally:
                logger.info(meth, **attrs.model_dump(exclude_none=True))
                set_otel_attrs_on_span(span, model_as_otel_attrs(attrs, prefix=meth))

    @classmethod
    def _auto_instrument(cls) -> None:
        """Auto-instrument an InstrumentRocqCursor deriver based on configs."""
        for fn_nm, fn_trace_kwargs in cls._instrument_kwargs().items():
            assert hasattr(cls, fn_nm), "ensured by _trace_targets"
            fn = getattr(cls, fn_nm)
            assert callable(fn), "ensured by _trace_targets"
            assert isinstance(fn, FunctionType), "ensured by _trace_targets"

            setattr(cls, fn_nm, override(cls._instrument(**fn_trace_kwargs)(fn)))

    @classmethod
    def _instrument[**P, A, B, T](
        cls,
        *,
        method: str | None = None,
        effect: (
            Callable[
                [InstrumentRocqCursor, dict[str, Any]],
                Awaitable[
                    tuple[str, Literal["blanks", "command", "ghost"]] | bool | None
                ],
            ]
            | Callable[
                [InstrumentRocqCursor, dict[str, Any]],
                tuple[str, Literal["blanks", "command", "ghost"]] | bool | None,
            ]
            | bool
            | None
        ) = None,
        partial_effect: bool = False,
    ) -> Callable[
        [Callable[Concatenate[Self, P], Coroutine[A, B, T]]],
        Callable[Concatenate[Self, P], CoroutineType[A, B, T]],
    ]:
        """Internal decorator: use opentelemetry to instrument a TracingCursor method.

        Arguments:
            method (optional): name to use instead of the method name
            effect (optional): characterize the effect & control whether after_id is generated (use
                most specific):
                - Callable: use self+args_dict to produce either:
                  - the text+kind for a /single/ document interaction
                  - a boolean indicating whether there was an effect
                - bool: whether a document effect was produced (either via navigation or a
                  composite interaction)
                - None (default): no document interaction
            partial_effect (optional): whether partial effects remain if rdm_api.Err is returned
        Returns:
            instrumented method
        """

        def wrap(func: Callable[P, Coroutine[A, B, T]]):
            sig = inspect.signature(func)
            meth = f"RocqCursor.{method or func.__name__}"

            @functools.wraps(func)
            async def wrapper(self, *args: P.args, **kwargs: P.kwargs):
                bound_args = sig.bind(self, *args, **kwargs)
                bound_args.apply_defaults()
                args_dict = dict(bound_args.arguments)
                args_dict.pop("self", None)

                attrs = InstrumentRocqCursorSpanAttrs.model_construct(
                    args={
                        k: v
                        for k, v in args_dict.items()
                        if not cls.auto_instrument_skip_value(v)
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
                        attrs.before = LocationInfo(
                            **await self._untraced_location_info()
                        )

                        result = await func(self, *args, **kwargs)

                        if result is not None:
                            attrs.error = isinstance(result, rdm_api.Err)
                            attrs.result_type = str(type(result))
                            if not cls.auto_instrument_skip_value(result):
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

    @classmethod
    def _instrument_kwargs(cls) -> dict[str, dict[str, Any]]:
        skip = cls.auto_instrument_skip()
        custom_trace_kwargs = cls.custom_instrument_kwargs()

        assert not (skip & set(custom_trace_kwargs.keys())), (
            f"skip:\n{skip}\nand custom_trace_kwargs:\n{custom_trace_kwargs}\nshould not overlap"
        )
        assert set(get_protocol_members(RocqCursor)) <= set(dir(cls)), (
            f"{cls.__qualname__} must implement the RocqCursor interface:{cls.__qualname__}",
        )

        targets: dict[str, dict[str, Any]] = {}
        for target_nm in (
            {
                attr_nm
                for attr_nm in get_protocol_members(RocqCursor)
                if callable(getattr(RocqCursor, attr_nm))
            }
            | custom_trace_kwargs.keys()
        ) - skip:
            assert hasattr(cls, target_nm), f"{cls.__qualname__} missing {target_nm}"
            target_fn = getattr(cls, target_nm)
            assert callable(target_fn), (
                f"{cls.__qualname__}.{target_nm} is not Callable: {repr(target_fn)}"
            )
            assert isinstance(target_fn, FunctionType), (
                f"{cls.__qualname__}.{target_nm} should be a function: {repr(target_fn)}"
            )

            if target_nm in custom_trace_kwargs:
                targets[target_nm] = custom_trace_kwargs[target_nm]
            else:
                targets[target_nm] = {}

        return targets

    async def _untraced_maybe_next_action(
        self, args: dict[str, Any]
    ) -> tuple[str, Literal["blanks", "command", "ghost"]] | None:
        if suffix := await self._cursor.doc_suffix():
            return (suffix[0].text, suffix[0].kind)
        else:
            return None

    async def _untraced_location_info(self) -> dict[str, Any]:
        """Construct a functional location by computing the hash of the effectful commands."""
        prefix = await self._cursor.doc_prefix()
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
