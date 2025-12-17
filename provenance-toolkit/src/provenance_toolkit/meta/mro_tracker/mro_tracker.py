"""Extensible metaclass for tracking inheritance hierarchy information, including selected methods & computed data.

This module provides a metaclass that can be extended to track and gather
inheritance hierarchy information from all points. Decorators are used to tag
methods and computed data as part of the inheritance hierarchy, and these tags are automatically
propagated to derivers.
"""

from __future__ import annotations

import inspect
import logging
from abc import ABCMeta
from types import FunctionType
from typing import Any, cast, final, overload

from provenance_toolkit.method_types import MethodTypes

from .mro_tracker_data import MROTrackerData, MROTrackerDatum, update_dict_of_containers

logger = logging.getLogger(__name__)


class MROTrackerMeta(ABCMeta):
    """Extensible tracking of inheritance hierarchies, including selected methods & computed data.

    By default, only class/base information is tracked; method/property tracking is opted into
    via the use of decorators (and automatic propogation of generated tags).

    This metaclass provides a framework for tracking inheritance hierarchy information:
    - Derivation hierarchy information
    - Method tracking information
    - Computed data tracking information

    Extensible decorators are exposed to allow derivers to customize the behavior of the framework.
    The following decorators are exposed by default:
    - @MROTrackerMeta.track: mark a method or property as tracked
    - @MROTrackerMeta.compute: mark a no-argument method or property as computing extra data

    Public API
    ----------
    The following methods provide the public interface for gathering data:

    - `gather_cls_data[T](cls: type[T]) -> MROTrackerData[T]`:
        Gather class-level data from all classes in the inheritance hierarchy of `cls`.
        Returns a MROTrackerData object for the class.

    - `gather_instance_data[T](instance: T) -> MROTrackerData[T]`:
        Gather instance-level data from all classes in the inheritance hierarchy of `instance`.
        Returns a MROTrackerData object for the instance.

    Cooperative Extension
    ---------------------
    The framework supports cooperative extension through multiple inheritance of metaclasses.
    When gathering data, the framework:

    1. Walks through the MRO of the class / instance
    2. Gathers MROTrackerDatum objects for each class / instance in the MRO -- collecting attributes from the
       MROTrackerDatum.TRACKING_ATTR_PREFIX namespace.

    This allows multiple metaclasses to extend data gathering by using adding custom attributes via
    MROTrackerData.add_tag_to; decorator factories exist to help with constructing derived decorators.

    Example
    -------
    TODO: Add example after finalizing implementation / decorator interface.
    """

    def __new__(
        mcs: type[MROTrackerMeta],
        name: str,
        bases: tuple[type, ...],
        namespace: dict[str, Any],
        **kwargs: Any,
    ) -> MROTrackerMeta:
        """Create a new class with transitive method/property tracking."""
        # Perform transitive method/property tracking and mutate namespace as necessary
        mcs._transitive_tracking(name, bases, namespace)
        return super().__new__(mcs, name, bases, namespace, **kwargs)

    @classmethod
    def _transitive_tracking(
        mcs: type[MROTrackerMeta],
        name: str,
        bases: tuple[type, ...],
        namespace: dict[str, Any],
    ) -> None:
        """Perform transitive code tracking and mutate namespace as necessary."""
        all_tracked_methods: dict[str, dict[str, Any]] = {}
        all_tracked_methods_compute_extra: dict[str, set[str]] = {
            kind: set() for kind in MROTrackerDatum.mro_tracker_method_kinds()
        }
        tracked_methods: dict[str, dict[str, Any]] = {}
        tracked_methods_compute_extra: dict[str, set[str]] = {
            kind: set() for kind in MROTrackerDatum.mro_tracker_method_kinds()
        }

        attr_prefix = MROTrackerData.mro_tracker_attr_prefix()

        assert attr_prefix not in namespace, (
            f"MROTrackerMeta error: {name} shouldn't define {attr_prefix} directly"
        )

        # Get MROTrackingDatum for bases; accumulate union of transitively tracked methods/properties
        base_tracking_data: dict[type, MROTrackerDatum[Any]] = {}
        for base in bases:
            if base in base_tracking_data:
                assert base_tracking_data[base] == MROTrackerDatum.build(klass=base), (
                    f"MROTrackerMeta error: {base_tracking_data[base]} != {MROTrackerDatum.build(klass=base)}"
                )
            else:
                base_tracking_data[base] = MROTrackerDatum.build(klass=base)
            update_dict_of_containers(
                a=all_tracked_methods,
                b=base_tracking_data[base].all_tracked_methods,
            )
            for kind in MROTrackerDatum.mro_tracker_method_kinds():
                all_tracked_methods_compute_extra[kind] |= base_tracking_data[
                    base
                ].all_tracked_methods_compute_extra[kind]

        # For all_tracked_methods: add missing attrs to methods present in namespace
        for base_tracking_datum in base_tracking_data.values():
            for (
                method_name,
                method_info,
            ) in base_tracking_datum.all_tracked_methods.items():
                if method_name not in namespace:
                    continue  # not actually in this class

                method = namespace[method_name]

                if not MethodTypes.is_method(method):
                    raise ValueError(
                        f"MROTrackerMeta error: {name}.{method_name} is not a method; {method}"
                    )

                for tracking_attr, value in method_info.items():
                    if hasattr(method, tracking_attr):
                        continue
                    object.__setattr__(method, tracking_attr, value)
                    logger.debug(
                        "Auto-tracked method attr: %s.%s.%s = %s",
                        name,
                        method_name,
                        tracking_attr,
                        value,
                    )

        # Update the following dicts with locally tracked methods/properties:
        # - all_tracked_methods
        # - all_tracked_methods_compute_extra
        # - tracked_methods
        # - tracked_methods_compute_extra
        for nm, value in namespace.items():
            if not MethodTypes.is_method(value):
                continue
            method_nm = nm
            method = value

            tracking_attrs = MROTrackerDatum.mro_tracker_lookup_all(method)

            if not hasattr(
                method, MROTrackerDatum.mro_tracker_namespaced_attr(attr="tracked")
            ):
                continue

            update_dict_of_containers(
                a=all_tracked_methods,
                b={method_nm: tracking_attrs},
            )
            update_dict_of_containers(
                a=tracked_methods,
                b={method_nm: tracking_attrs},
            )

            for kind in MROTrackerDatum.mro_tracker_method_kinds():
                if (
                    MROTrackerDatum.mro_tracker_namespaced_attr(attr=kind)
                    not in tracking_attrs
                ):
                    continue

                match kind:
                    case "staticmethod":
                        assert MethodTypes.is_staticmethod(method) or (
                            MethodTypes.is_property(method)
                            and isinstance(method.fget, staticmethod)
                        ), f"MROTrackerMeta error: {method} is not a staticmethod"
                    case "classmethod":
                        assert MethodTypes.is_classmethod(method), (
                            f"MROTrackerMeta error: {method} is not a classmethod"
                        )
                    case "boundmethod":
                        assert MethodTypes.is_boundmethod(method) or (
                            MethodTypes.is_property(method)
                            and isinstance(method.fget, FunctionType)
                        ), f"MROTrackerMeta error: {method} is not a boundmethod"
                    case "property":
                        assert MethodTypes.is_property(method), (
                            f"MROTrackerMeta error: {method} is not a property"
                        )
                    case _:
                        raise ValueError(
                            f"MROTrackerMeta error: invalid method kind: {kind}"
                        )

                all_tracked_methods_compute_extra[kind].add(method_nm)
                tracked_methods_compute_extra[kind].add(method_nm)

        namespace[attr_prefix] = MROTrackerDatum(
            cls=mcs,
            bases=bases,
            all_tracked_methods=all_tracked_methods,
            all_tracked_methods_compute_extra=all_tracked_methods_compute_extra,
            tracked_methods=tracked_methods,
            tracked_methods_compute_extra=tracked_methods_compute_extra,
        )

    # Decorator methods

    # Note: mypy gets confused since MethodTypes.STATICMETHOD[P, T] doesn't take the
    # same number of type parameters as MethodTypes.METHOD[O, P, T]
    @staticmethod  # type: ignore[no-overload-impl]
    @overload
    def track[**P, T](
        fn: MethodTypes.STATICMETHOD[P, T],
    ) -> MethodTypes.STATICMETHOD[P, T]:
        """Decorator: track staticmethod fn so it is tracked."""

    @staticmethod
    @overload
    def track[O, **P, T](
        fn: MethodTypes.CLASSMETHOD[O, P, T],
    ) -> MethodTypes.CLASSMETHOD[O, P, T]:
        """Decorator: track classmethod fn so it is tracked."""

    @staticmethod
    @overload
    def track[O, **P, T](
        fn: MethodTypes.BOUNDMETHOD[O, P, T],
    ) -> MethodTypes.BOUNDMETHOD[O, P, T]:
        """Decorator: track bound method fn so it is tracked."""

    # Note: mypy gets confused since MethodTypes.PROPERTY doesn't take the
    # same number of type parameters as MethodTypes.METHOD[O, P, T]
    @staticmethod  # type: ignore[no-overload-impl]
    @overload
    def track(
        fn: MethodTypes.PROPERTY,
    ) -> MethodTypes.PROPERTY:
        """Decorator: track property so it is tracked."""

    # Note: mypy gets confused since MethodTypes.PROPERTY doesn't take the
    # same number of type parameters as MethodTypes.METHOD[O, P, T]
    @staticmethod  # type: ignore[no-overload-impl]
    @overload
    def compute[T](
        fn: MethodTypes.STATICMETHOD[[], T],
    ) -> MethodTypes.STATICMETHOD[[], T]:
        """Decorator: track + use staticmethod fn to compute extra data."""

    @staticmethod
    @overload
    def compute[O, T](
        fn: MethodTypes.CLASSMETHOD[O, [], T],
    ) -> MethodTypes.CLASSMETHOD[O, [], T]:
        """Decorator: track + use classmethod fn to compute extra data."""

    @staticmethod
    @overload
    def compute[O, T](
        fn: MethodTypes.BOUNDMETHOD[O, [], T],
    ) -> MethodTypes.BOUNDMETHOD[O, [], T]:
        """Decorator: track + use bound method fn to compute extra data."""

    # Note: mypy gets confused since MethodTypes.PROPERTY doesn't take the
    # same number of type parameters as MethodTypes.METHOD[O, P, T]
    @staticmethod  # type: ignore[no-overload-impl]
    @overload
    def compute(
        fn: MethodTypes.PROPERTY,
    ) -> MethodTypes.PROPERTY:
        """Decorator: track + use property to compute extra data."""

    @final  # type: ignore[no-redef]
    @staticmethod
    def track[O, **P, T](
        fn: MethodTypes.METHOD[O, P, T],
    ) -> MethodTypes.METHOD[O, P, T]:
        """Decorator: track fn/property so it is tracked."""
        tracking_attrs: set[str]
        assert MethodTypes.is_method(fn), f"MROTrackerMeta.track: {fn} is not a method"

        if MethodTypes.is_staticmethod(fn):
            tracking_attrs = MROTrackerDatum.mro_tracker_method_kind_to_attrs()[
                "staticmethod"
            ]
        elif MethodTypes.is_classmethod(fn):
            tracking_attrs = MROTrackerDatum.mro_tracker_method_kind_to_attrs()[
                "classmethod"
            ]
        elif MethodTypes.is_boundmethod(fn):
            tracking_attrs = MROTrackerDatum.mro_tracker_method_kind_to_attrs()[
                "boundmethod"
            ]
        elif MethodTypes.is_property(fn):
            tracking_attrs = MROTrackerDatum.mro_tracker_method_kind_to_attrs()[
                "property"
            ]
            if isinstance(fn.fget, staticmethod):
                tracking_attrs.add("staticmethod")
            elif isinstance(fn.fget, FunctionType):
                tracking_attrs.add("boundmethod")
            else:
                raise RuntimeError(
                    f"MROTrackerMeta.track: {fn} is not a static/bound property"
                )
        else:
            raise RuntimeError(f"{fn} is not a static/class/bound method")

        return MROTrackerMeta._track_method_as(fn, tracking_attrs=tracking_attrs)

    @final  # type: ignore[no-redef]
    @staticmethod
    def compute[O, T](
        fn: MethodTypes.METHOD[O, [], T],
    ) -> MethodTypes.METHOD[O, [], T]:
        """Decorator: track + use fn/property to compute extra data."""
        tracking_attrs: set[str]
        fn_raw: MethodTypes.RAW_METHOD[O, [], T]

        if MethodTypes.is_staticmethod(fn):
            fn_raw = fn.__func__
            tracking_attrs = MROTrackerDatum.mro_tracker_method_kind_to_attrs(
                compute_extra=True
            )["staticmethod"]
        elif MethodTypes.is_classmethod(fn):
            fn_raw = fn.__func__
            tracking_attrs = MROTrackerDatum.mro_tracker_method_kind_to_attrs(
                compute_extra=True
            )["classmethod"]
        elif MethodTypes.is_boundmethod(fn):
            fn_raw = fn
            tracking_attrs = MROTrackerDatum.mro_tracker_method_kind_to_attrs(
                compute_extra=True
            )["boundmethod"]
        elif MethodTypes.is_property(fn):
            tracking_attrs = MROTrackerDatum.mro_tracker_method_kind_to_attrs(
                compute_extra=True
            )["property"]
            if isinstance(fn.fget, staticmethod):
                fn_raw = fn.fget.__func__
                tracking_attrs.add("staticmethod")
            elif isinstance(fn.fget, FunctionType):
                fn_raw = fn.fget
                tracking_attrs.add("boundmethod")
            else:
                raise RuntimeError(
                    f"MROTrackerMeta.compute: {fn} is not a static/bound property"
                )
        else:
            raise RuntimeError(f"{fn} is not a static/class/bound method")

        # Validate 0-arg (excluding self/cls)
        try:
            sig = inspect.signature(fn_raw)
            param_list = list(sig.parameters.values())
            if MethodTypes.is_staticmethod(fn) or (
                MethodTypes.is_property(fn) and isinstance(fn.fget, staticmethod)
            ):
                if len(param_list) != 0:
                    raise ValueError(
                        f"@MROTrackerMeta.compute requires a 0-arg "
                        f"staticmethod, but {fn.__name__} has "
                        f"{len(param_list)} parameters"
                    )
            else:  # is_classmethod or is_boundmethod
                if len(param_list) != 1:
                    raise ValueError(
                        f"@MROTrackerMeta.compute requires a 0-arg "
                        f"classmethod/boundmethod (excluding self/cls), but "
                        f"{fn.__name__} has {len(param_list)} parameters"
                    )
                param = param_list[0]
                allowed_param_kinds = (
                    inspect.Parameter.POSITIONAL_ONLY,
                    inspect.Parameter.POSITIONAL_OR_KEYWORD,
                    inspect.Parameter.KEYWORD_ONLY,
                )
                if param.kind not in allowed_param_kinds:
                    raise ValueError(
                        f"@MROTrackerMeta.compute: invalid parameter kind "
                        f"for {fn.__name__}; {param.kind} not "
                        f" in {allowed_param_kinds}"
                    )
        except (ValueError, TypeError, OSError) as e:
            logger.warning(
                "Could not validate 0-arg requirement for %s: %s",
                fn.__name__,
                e,
            )

        assert MethodTypes.is_method(fn)
        return MROTrackerMeta._track_method_as(
            cast(MethodTypes.METHOD[O, [], T], fn),  # type: ignore[arg-type]
            tracking_attrs=tracking_attrs,
        )

    @final
    @classmethod
    def _track_method_as[O, **P, T](
        mcs: type[MROTrackerMeta],
        fn: MethodTypes.METHOD[O, P, T],
        tracking_attrs: set[str],
    ) -> MethodTypes.METHOD[O, P, T]:
        """Helper: annotate method with namespaced attrs."""
        assert MethodTypes.is_method(fn)

        for attr in tracking_attrs:
            MROTrackerDatum.mro_tracker_add_tag_to(obj=fn, attr=attr, v=True)

        return fn
