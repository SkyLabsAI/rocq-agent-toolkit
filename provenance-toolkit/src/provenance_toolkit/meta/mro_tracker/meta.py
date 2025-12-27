"""MROTrackerMeta: extensible metaclass for tracking inheritance hierarchy information.

This module provides a metaclass that can be extended to track and gather
inheritance hierarchy information from all points, including selected methods & computed data.
Decorators are used to tag methods and computed data as part of the inheritance hierarchy,
and these tags are automatically propagated to derivers.
"""

from __future__ import annotations

import logging
from abc import ABCMeta
from types import FunctionType
from typing import Any

from provenance_toolkit.method_types import MethodTypes

from .data import MROTrackerData, MROTrackerDatum, update_dict_of_dict
from .decorator import MROTrackerDecorator

logger = logging.getLogger(__name__)


class MROTrackerMeta(MROTrackerDecorator, ABCMeta):
    """Extensible tracking of inheritance hierarchies + selected methods & computed data.

    By default, only class/base information is tracked; method/property tracking is
    opted into via the use of decorators (and automatic propogation of generated tags).

    This metaclass provides a framework for tracking inheritance hierarchy information:
    - Derivation hierarchy information
    - Method tracking information
    - Computed data tracking information

    Extensible decorators are exposed to allow derivers to customize the behavior of the
    framework. The following decorators are exposed by default (cf. decorator.py):
    - @MROTrackerMeta.track: mark a method or property as tracked
    - @MROTrackerMeta.compute: mark a 0-arg method or property as computing extra data

    Cooperative Extension
    ---------------------
    The framework supports cooperative extension through multiple inheritance of
    metaclasses. When gathering data, the framework:
    1. Walks through the MRO of the class / instance gathering (base) class types
       at each point
    2. Gathers MROTrackerDatum objects for each class / instance in the MRO,
       collecting attributes from the MROTrackerDatum.TRACKING_ATTR_PREFIX namespace.

    This allows multiple metaclasses to extend data gathering by using custom attributes
    via MROTrackerData.add_tag_to; decorator factories exist to help with constructing
    derived decorators (cf. decorator.py).

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
                    "MROTrackerMeta error: "
                    f"{base_tracking_data[base]} != {MROTrackerDatum.build(klass=base)}"
                )
            else:
                base_tracking_data[base] = MROTrackerDatum.build(klass=base)
            update_dict_of_dict(
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
                        "MROTrackerMeta error: "
                        f"{name}.{method_name} is not a method; {method}"
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

            update_dict_of_dict(
                a=all_tracked_methods,
                b={method_nm: tracking_attrs},
            )
            update_dict_of_dict(
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
