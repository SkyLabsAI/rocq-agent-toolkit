"""MROTrackerDecorator: extensible decorator (factory) interface used by MROTrackerMeta.

Core decorators are exposed which track code and computed data in a generic way:
- @MROTrackerDecorator.track: mark a method or property as tracked
- @MROTrackerDecorator.compute: track + mark a 0-arg method/property to compute
  extra data
- @MROTrackerDecorator.track_as: mark a method or property as tracked, and include
  extra attributes

Decorator factories are exposed so derivers can easily track additional information:
- MROTrackerDecorator.mk_track(...): build a decorator that

See meta.py for more information.
"""

from __future__ import annotations

import inspect
import logging
from collections.abc import Callable
from types import FunctionType
from typing import Any, Literal, final

from provenance_toolkit.method_types import (
    AttributeSetter,
    MethodDecorator,
    MethodTypes,
    MethodWrapper,
    WrapperFunc,
)

from .data import MROTrackerDatum

logger = logging.getLogger(__name__)


class MROTrackerDecorator(MethodDecorator):
    """Decorators for tracking method/property registration and computed data."""

    @final
    @staticmethod
    def track[O, **P, T](
        fn: MethodTypes.RAW_METHOD[O, P, T] | MethodTypes.METHOD[O, P, T] | None = None,
        *,
        raw: bool | Literal[True] | Literal[False] = False,
    ) -> (
        MethodWrapper[O, P, T]
        | Callable[[MethodTypes.RAW_METHOD[O, P, T]], MethodWrapper[O, P, T]]
        | Callable[[MethodTypes.METHOD[O, P, T]], MethodWrapper[O, P, T]]
    ):
        """Decorator: track method/property fn."""
        return MROTrackerDecorator.track_as(fn=fn, compute_extra=False, raw=raw)

    @final
    @staticmethod
    def compute[O, T](
        fn: (
            MethodTypes.RAW_METHOD[O, [], T] | MethodTypes.METHOD[O, [], T] | None
        ) = None,
        *,
        raw: bool | Literal[True] | Literal[False] = False,
    ) -> (
        MethodWrapper[O, [], T]
        | Callable[[MethodTypes.RAW_METHOD[O, [], T]], MethodWrapper[O, [], T]]
        | Callable[[MethodTypes.METHOD[O, [], T]], MethodWrapper[O, [], T]]
    ):
        """Decorator: track + use fn/property to compute extra data."""
        return MROTrackerDecorator.track_as(
            fn=fn,
            wrapper_fn=MROTrackerDecorator._mk_validate_0_arg,
            compute_extra=True,
            raw=raw,
        )

    @final
    @staticmethod
    def track_as[O, **P, T](
        fn: MethodTypes.RAW_METHOD[O, P, T] | MethodTypes.METHOD[O, P, T] | None = None,
        *,
        wrapper_fn: WrapperFunc[O, P, T] | None = None,
        compute_extra: bool = False,
        extra_tracking_attrs: set[str] | None = None,
        raw: bool | Literal[True] | Literal[False] = False,
    ) -> (
        MethodWrapper[O, P, T]
        | Callable[[MethodTypes.RAW_METHOD[O, P, T]], MethodWrapper[O, P, T]]
        | Callable[[MethodTypes.METHOD[O, P, T]], MethodWrapper[O, P, T]]
    ):
        """Helper: annotate method with namespaced attrs."""
        return MethodDecorator.wrap(
            fn=fn,
            wrapper_fn=wrapper_fn,
            attribute_setter=MROTrackerDecorator._make_attribute_setter(
                compute_extra=compute_extra, extra_tracking_attrs=extra_tracking_attrs
            ),
            raw=raw,
        )

    @staticmethod
    def _mk_validate_0_arg[O, T](
        raw_fn: MethodTypes.RAW_METHOD[O, [], T],
        descriptor_metadata: dict[str, Any],
        _wrapper_args: tuple[Any, ...],
        _wrapper_kwargs: dict[str, Any],
    ) -> MethodTypes.RAW_METHOD[O, [], T]:
        """Validate that the raw function is 0-arg (excluding self/cls) and return it unchanged.

        This is used as a wrapper_fn to validate compute methods before they are tracked.
        """
        descriptor_type = descriptor_metadata.get("descriptor_type")
        property_getter_type = descriptor_metadata.get("property_getter_type")

        # Validate 0-arg (excluding self/cls)
        try:
            sig = inspect.signature(raw_fn)
            param_list = list(sig.parameters.values())

            is_static = descriptor_type is staticmethod or (
                descriptor_type is property and property_getter_type is staticmethod
            )

            if is_static:
                if len(param_list) != 0:
                    raise ValueError(
                        f"@MROTrackerDecorator.compute requires a 0-arg "
                        f"staticmethod, but {raw_fn.__name__} has "
                        f"{len(param_list)} parameters"
                    )
            else:  # is_classmethod or is_boundmethod
                if len(param_list) != 1:
                    raise ValueError(
                        f"@MROTrackerDecorator.compute requires a 0-arg "
                        f"classmethod/boundmethod (excluding self/cls), but "
                        f"{raw_fn.__name__} has {len(param_list)} parameters"
                    )
                param = param_list[0]
                allowed_param_kinds = (
                    inspect.Parameter.POSITIONAL_ONLY,
                    inspect.Parameter.POSITIONAL_OR_KEYWORD,
                    inspect.Parameter.KEYWORD_ONLY,
                )
                if param.kind not in allowed_param_kinds:
                    raise ValueError(
                        f"@MROTrackerDecorator.compute: invalid parameter kind "
                        f"for {raw_fn.__name__}; {param.kind} not "
                        f" in {allowed_param_kinds}"
                    )
        except (ValueError, TypeError, OSError) as e:
            logger.warning(
                "Could not validate 0-arg requirement for %s: %s",
                raw_fn.__name__,
                e,
            )

        return raw_fn

    @staticmethod
    def _make_attribute_setter[O, **P, T](
        compute_extra: bool = False,
        extra_tracking_attrs: set[str] | None = None,
    ) -> AttributeSetter[O, P, T]:
        """Create an attribute setter function for track_as functionality."""
        if extra_tracking_attrs is None:
            extra_tracking_attrs = set()

        def attribute_setter(
            final_descriptor: (
                MethodTypes.RAW_METHOD[O, P, T] | MethodTypes.METHOD[O, P, T]
            ),
            descriptor_metadata: dict[str, Any],
            _wrapper_args: tuple[Any, ...],
            _wrapper_kwargs: dict[str, Any],
        ) -> None:
            """Add tracking attributes to the final descriptor."""
            tracking_attrs: set[str]
            descriptor_type = descriptor_metadata.get("descriptor_type")
            property_getter_type = descriptor_metadata.get("property_getter_type")

            if descriptor_type is staticmethod:
                tracking_attrs = MROTrackerDatum.mro_tracker_method_kind_to_attrs(
                    compute_extra=compute_extra,
                )["staticmethod"]
                # For staticmethod, final_descriptor is the staticmethod instance
                target_obj = final_descriptor
            elif descriptor_type is classmethod:
                tracking_attrs = MROTrackerDatum.mro_tracker_method_kind_to_attrs(
                    compute_extra=compute_extra,
                )["classmethod"]
                # For classmethod, if final_descriptor is a bound method, we can't
                # set attributes on it. We set attributes on the underlying function instead.
                # The attributes will be accessible via the function.
                if isinstance(final_descriptor, classmethod):
                    target_obj = final_descriptor
                elif isinstance(final_descriptor, FunctionType):
                    # It's a bound method (FunctionType), set attributes on the function itself
                    target_obj = final_descriptor
                elif hasattr(final_descriptor, "__func__"):
                    target_obj = object.__getattribute__(final_descriptor, "__func__")
                else:
                    target_obj = final_descriptor
            elif descriptor_type is property:
                tracking_attrs = MROTrackerDatum.mro_tracker_method_kind_to_attrs(
                    compute_extra=compute_extra,
                )["property"]
                if property_getter_type is staticmethod:
                    tracking_attrs.add("staticmethod")
                elif property_getter_type is None:
                    # None means it's a bound method property
                    tracking_attrs.add("boundmethod")
                # For property, if final_descriptor is a property value, we need to
                # set attributes on the property object, not the value
                if isinstance(final_descriptor, property):
                    target_obj = final_descriptor
                else:
                    # It's a property value, we can't set attributes on it
                    target_obj = None
            elif descriptor_type is None:
                # Bound method or free function
                tracking_attrs = MROTrackerDatum.mro_tracker_method_kind_to_attrs(
                    compute_extra=compute_extra,
                )["boundmethod"]
                # For bound methods, we can set attributes on the function itself
                # final_descriptor might be a bound method or the raw function
                if isinstance(final_descriptor, FunctionType):
                    target_obj = final_descriptor
                elif hasattr(final_descriptor, "__func__"):
                    # It's a bound method, set attributes on the underlying function
                    target_obj = object.__getattribute__(final_descriptor, "__func__")
                else:
                    target_obj = final_descriptor
            else:
                raise RuntimeError(
                    f"MROTrackerDecorator: unknown descriptor_type {descriptor_type}"
                )

            # Set attributes on the target object
            if target_obj is not None:
                for attr in tracking_attrs | extra_tracking_attrs:
                    try:
                        MROTrackerDatum.mro_tracker_add_tag_to(
                            obj=target_obj, attr=attr, v=True
                        )
                    except (AttributeError, TypeError):
                        # Some objects don't support setting attributes
                        pass

        return attribute_setter
