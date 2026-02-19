"""
This file collects decorators for use with RocqCursor and other Rocq APIs.
"""

from __future__ import annotations

import functools
import inspect
import logging
from collections.abc import Callable, Collection
from types import FunctionType
from typing import cast, get_type_hints

logger = logging.getLogger(__name__)


# TODO: simplify this with use of `wrapt` once opentelemetry-python-contrib
# relaxes too-strict version constraints.
#
# cf. https://github.com/open-telemetry/opentelemetry-python-contrib/pull/3930
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
                        resolved_annotation = type_hints.get(argname, param.annotation)
                    except Exception:
                        # If get_type_hints fails, use the annotation as-is
                        resolved_annotation = param.annotation

                    # Check if annotation is str type (handle both str type and "str" string)
                    if resolved_annotation is not str and resolved_annotation != "str":
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
                    resolved_annotation = type_hints.get("return", return_annotation)
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
