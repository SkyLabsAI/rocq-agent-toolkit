"""Data types & utilities used by mro_tracker.py for tracking inheritance hierarchy information."""

from __future__ import annotations

import logging
from copy import deepcopy
from dataclasses import dataclass, field
from types import FunctionType
from typing import Any, Literal, overload

from provenance_toolkit.method_types import MethodTypes

logger = logging.getLogger(__name__)

def update_dict_of_containers[C: dict[str, dict[str, Any]]](a: C, b: C) -> C:
    """Update dict of containers (a) with the contents of another dict of containers (b)."""
    for k, v in b.items():
        if k in a:
            a[k].update(v)
        else:
            a[k] = deepcopy(v)
    return a


class MROTrackerDataMixin:
    """Mixin: utilities for working with tracking attributes in MROTrackerDatum & MROTrackerData."""

    @classmethod
    def mro_tracker_attr_prefix(
        cls: type[MROTrackerDataMixin],
    ) -> str:
        """The prefix for the namespaced attributes."""
        return "__mro_tracker"

    @classmethod
    def mro_tracker_reserved_attrs(
        cls: type[MROTrackerDataMixin],
    ) -> set[str]:
        """The reserved attributes."""
        return deepcopy(
            {
                cls.mro_tracker_attr_prefix(),
                "tracked",
                "staticmethod",
                "classmethod",
                "boundmethod",
                "property",
                "compute_extra",
            }
        )

    @classmethod
    def mro_tracker_method_kinds(
        cls: type[MROTrackerDataMixin],
    ) -> tuple[str, str, str, str]:
        """The method kinds."""
        return ("staticmethod", "classmethod", "boundmethod", "property")

    @classmethod
    def mro_tracker_method_kind_to_attrs(
        cls: type[MROTrackerDataMixin],
        compute_extra: bool = False,
    ) -> dict[str, set[str]]:
        """The method kind to track attribute map."""
        if compute_extra:
            extra_attrs = {"compute_extra"}
        else:
            extra_attrs = set()

        return {
            "staticmethod": {"tracked", "staticmethod"} | extra_attrs,
            "classmethod": {"tracked", "classmethod"} | extra_attrs,
            "boundmethod": {"tracked", "boundmethod"} | extra_attrs,
            "property": {"tracked", "property"} | extra_attrs,
        }

    @classmethod
    def mro_tracker_namespaced_attr(
        cls: type[MROTrackerDataMixin],
        attr: str | None = None,
    ) -> str:
        """Generate a namespaced attribute name for a given attribute."""
        if attr is None:
            return cls.mro_tracker_attr_prefix()
        return f"{cls.mro_tracker_attr_prefix()}_{attr}"

    @classmethod
    def mro_tracker_add_tag_to(
        cls: type[MROTrackerDataMixin],
        obj: Any,
        attr: str | None = None,
        v: Any = None,
    ) -> None:
        """Add a namespaced attribute to an object, for later lookup."""
        object.__setattr__(obj, cls.mro_tracker_namespaced_attr(attr=attr), v)

    @classmethod
    @overload
    def mro_tracker_lookup[X](
        cls: type[MROTrackerDataMixin],
        obj: Any,
        *,
        attr: str | None = None,
        attr_ty: type[X],
        strict: Literal[True] = True,
    ) -> X:
        """Lookup namespaced_attr(attr) in obj.__dict__, raising error on failure."""

    @classmethod
    @overload
    def mro_tracker_lookup[X](
        cls: type[MROTrackerDataMixin],
        obj: Any,
        *,
        attr: str | None = None,
        attr_ty: type[X] | None = None,
        strict: Literal[True] = True,
    ) -> X | None:
        """Lookup namespaced_attr(attr) in obj.__dict__, returning the value if present."""

    @classmethod
    @overload
    def mro_tracker_lookup[X](
        cls: type[MROTrackerDataMixin],
        obj: Any,
        *,
        attr: str | None = None,
        attr_ty: type[X] | None = None,
        strict: bool | Literal[False],
    ) -> X | None:
        """Lookup namespaced_attr(attr) in obj.__dict__, returning the value if present."""

    @classmethod
    def mro_tracker_lookup[X](
        cls: type[MROTrackerDataMixin],
        obj: Any,
        *,
        attr: str | None = None,
        attr_ty: type[X] | None = None,
        strict: bool | Literal[True] | Literal[False] = True,
    ) -> X | None:
        """Lookup namespaced_attr(attr) in obj.__dict__, returning the value if present.

        Returns:
          - Value of namespaced_attr(attr) for obj, if present
          - None, if namespaced_attr(attr) is missing for obj and strict=False

        Raises:
          - ValueError, if namespaced_attr(attr) is missing and strict=True.
          - TypeError, if getattr(obj, namespaced_attr(attr)) is ill-typed and strict=True.
        """
        attrs = cls.mro_tracker_lookup_all(obj=obj)
        attr = cls.mro_tracker_namespaced_attr(attr=attr)

        if attr not in attrs:
            msg = f"MROTrackerDatum error: {obj.__qualname__} missing {attr}: {obj.__dict__.keys()}"
            if strict:
                raise ValueError(msg)
            else:
                logger.warning(msg)
                return None

        attr_value: Any = attrs[attr]
        if attr_ty is not None and not isinstance(attr_value, attr_ty):
            msg = " ".join(
                [
                    f"MROTrackerDatum error: {obj.__qualname__}.{attr} ill typed;",
                    f"expected {attr_ty} but got {type(attr_value)}",
                ]
            )
            if strict:
                raise TypeError(msg)
            else:
                logger.warning(msg)
                return None

        return attr_value

    @classmethod
    def mro_tracker_lookup_all(cls: type[MROTrackerDataMixin], obj: Any) -> dict[str, Any]:
        """Lookup all namespaced attributes in obj.__dict__."""
        return {k: v for k, v in obj.__dict__.items() if k.startswith(cls.mro_tracker_attr_prefix)}


@dataclass(frozen=True)
class MROTrackerDatum[T](MROTrackerDataMixin):
    """Inheritance hierarchy information for a single class or instance.

    This dataclass stores information about which methods are tracked and
    which methods compute extra data. It's used internally by the framework
    to track method registration across the inheritance hierarchy. Tracked
    data includes:
    - cls: the class
    - for cls:
        - bases: the bases
        - transitively defined method/property tracking information:
          - all_tracked_methods: all methods defined and tracked
          - all_tracked_properties: all properties defined and tracked
          - all_tracked_methods_compute_extra: map from method kind to sets of method/property names
            that compute extra data
        - locally defined method/property tracking information:
          - tracked_methods: the methods that are tracked; map from method names to tracking attr
            KV pairs
          - tracked_properties: the properties that are tracked; map from property names to tracking
            attr KV pairs
          - tracked_methods_compute_extra: map from method kind to sets of method/property names
            that compute extra data
    """

    cls: type[T] = field(kw_only=True)
    bases: list[type] = field(kw_only=True)
    all_tracked_methods: dict[str, dict[str, Any]] = field(kw_only=True, default_factory=dict)
    all_tracked_methods_compute_extra: dict[str, set[str]] = field(kw_only=True, default_factory=dict)
    tracked_methods: dict[str, dict[str, Any]] = field(kw_only=True, default_factory=dict)
    tracked_methods_compute_extra: dict[str, set[str]] = field(kw_only=True, default_factory=dict)
    tracked_methods_compute_extra_data: dict[str, Any] | None = field(kw_only=True, default=None)

    @classmethod
    def build[X](
        cls: type[MROTrackerDatum[X]],
        klass: type[X],
    ) -> MROTrackerDatum[X]:
        """Build a MROTrackerDatum object for a given class."""
        all_tracked_methods: dict[str, dict[str, Any]] = {}
        all_tracked_methods_compute_extra: dict[str, set[str]] = {
            kind: set() for kind in cls.mro_tracker_method_kinds()
        }
        tracked_methods: dict[str, dict[str, Any]] = {}
        tracked_methods_compute_extra: dict[str, set[str]] = {
            kind: set() for kind in cls.mro_tracker_method_kinds()
        }

        # 1. Accumulate union of transitively tracked methods from bases
        for base in klass.__bases__:
            maybe_tracking = cls.mro_tracker_lookup(
                obj=base,
                attr_ty=MROTrackerDatum[T],
                strict=False,
            )
            if maybe_tracking is not None:
                all_tracked_methods = update_dict_of_containers(
                    a=all_tracked_methods,
                    b=maybe_tracking.all_tracked_methods,
                )
                for kind in cls.mro_tracker_method_kinds():
                    all_tracked_methods_compute_extra[kind] |= (
                        maybe_tracking.all_tracked_methods_compute_extra[kind]
                    )

        # 2. Accumulate locally tracked methods
        #
        # Note: adding/propagating attrs is handled mro_tracker.py#MROTracker.
        for member_name, member_value in klass.__dict__.items():
            if not MethodTypes.is_method(member_value):
                continue

            if not hasattr(member_value, cls.mro_tracker_namespaced_attr(attr="tracked")):
                continue

            matches: set[str] = set()
            for kind in cls.mro_tracker_method_kinds():
                if not all(
                    hasattr(member_value, cls.mro_tracker_namespaced_attr(attr=attr))
                    for attr in cls.mro_tracker_method_kind_to_attrs()[kind]
                ):
                    continue
                matches.add(kind)

                member_info = {
                        attr: value
                        for attr, value in member_value.__dict__.items()
                        if attr.startswith(cls.mro_tracker_attr_prefix())
                }
                all_tracked_methods = update_dict_of_containers(
                    a=all_tracked_methods,
                    b={member_name: member_info}
                )
                tracked_methods = update_dict_of_containers(
                    a=tracked_methods,
                    b={member_name: member_info},
                )

                maybe_compute_extra = MROTrackerDatum.mro_tracker_lookup(
                    obj=member_value, attr="compute_extra",
                )
                if maybe_compute_extra is not None:
                    all_tracked_methods_compute_extra[kind] |= member_name
                    tracked_methods_compute_extra[kind] |= member_name

        return cls(
            cls=klass,
            bases=list(klass.__bases__),
            all_tracked_methods=all_tracked_methods,
            all_tracked_methods_compute_extra=all_tracked_methods_compute_extra,
            tracked_methods=tracked_methods,
            tracked_methods_compute_extra=tracked_methods_compute_extra,
        )

    def compute_extra(self, instance: T | None = None) -> MROTrackerDatum[T]:
        """Run the locally defined methods that compute extra data and return a new MROTrackerDatum with the computed data."""
        if instance is not None:
            assert issubclass(type(instance), self.cls), (
                f"MROTrackerDatum error: instance is not a subclass of cls: {type(instance)} is not a subclass of {self.cls}"
            )

        tracked_methods_compute_extra_data: dict[str, Any] = {}
        kinds = ["staticmethod", "classmethod"] + ([] if instance is None else ["boundmethod"])
        for kind in kinds:
            for method_name in self.tracked_methods_compute_extra[kind]:
                method: MethodTypes.METHOD[T, [], Any] = getattr(self.cls, method_name)
                assert MethodTypes.is_method(method), f"MROTrackerDatum error: {method} is not a method"

                if kind == "staticmethod":
                    raw_staticmethod: MethodTypes.RAW_STATICMETHOD[[], Any]
                    if MethodTypes.is_property(method) and isinstance(method.fget, staticmethod):
                        raw_staticmethod = method.fget.__func__
                    elif MethodTypes.is_staticmethod(method):
                        raw_staticmethod = method.__func__
                    else:
                        raise ValueError(f"MROTrackerDatum error: {method} is not a staticmethod")
                    tracked_methods_compute_extra_data[method_name] = raw_staticmethod()
                elif kind == "classmethod":
                    assert MethodTypes.is_classmethod(method), f"MROTrackerDatum error: {method} is not a classmethod"
                    raw_classmethod: MethodTypes.RAW_CLASSMETHOD[T, [], Any] = method.__func__
                    tracked_methods_compute_extra_data[method_name] = raw_classmethod(self.cls)
                elif kind == "boundmethod":
                    assert instance is not None, f"MROTrackerDatum error: instance is None for boundmethod: {method_name}"
                    raw_boundmethod: MethodTypes.RAW_BOUNDMETHOD[T, [], Any]
                    if MethodTypes.is_property(method) and isinstance(method.fget, FunctionType):
                        raw_boundmethod = method.fget
                    elif MethodTypes.is_boundmethod(method):
                        raw_boundmethod = method
                    else:
                        raise ValueError(f"MROTrackerDatum error: {method} is not a boundmethod")
                    tracked_methods_compute_extra_data[method_name] = raw_boundmethod(instance)
                else:
                    raise ValueError(f"MROTrackerDatum error: invalid method kind: {kind}")

        return self.__class__(
            cls=self.cls,
            bases=self.bases,
            all_tracked_methods=self.all_tracked_methods,
            all_tracked_methods_compute_extra=self.all_tracked_methods_compute_extra,
            tracked_methods=self.tracked_methods,
            tracked_methods_compute_extra=self.tracked_methods_compute_extra,
            tracked_methods_compute_extra_data=tracked_methods_compute_extra_data,
        )

    def __post_init__(self) -> None:
        """Validate tracking data consistency."""
        assert self.tracked_methods.keys() <= self.all_tracked_methods.keys(), (
            f"MROTrackerDatum error: {self.tracked_methods.keys()} not tracked transitively: "
            f"{self.tracked_methods.keys() - self.all_tracked_methods.keys()}"
        )
        for method_name, method_info in self.tracked_methods.items():
            for key, value in method_info.items():
                assert key in self.all_tracked_methods[method_name], (
                    f"MROTrackerDatum error: {key} not tracked transitively: "
                    f"{key - self.all_tracked_methods[method_name].keys()}"
                )
                tracked_value = self.all_tracked_methods[method_name][key]
                assert value == tracked_value, (
                    f"MROTrackerDatum error: {value} != {tracked_value}"
                )

        assert self.all_tracked_methods_compute_extra.keys() == self.mro_tracker_method_kinds(), (
            f"MROTrackerDatum error: all_tracked_methods_compute_extra keys != METHOD_KINDS: "
            f"{self.all_tracked_methods_compute_extra.keys() - self.mro_tracker_method_kinds()}"
        )
        assert self.tracked_methods_compute_extra.keys() == self.mro_tracker_method_kinds(), (
            f"MROTrackerDatum error: all_tracked_methods_compute_extra keys != METHOD_KINDS: "
            f"{self.tracked_methods_compute_extra.keys() - self.mro_tracker_method_kinds()}"
        )

        for all_items, items in [
            *[
                (
                    self.all_tracked_methods_compute_extra[kind],
                    self.tracked_methods_compute_extra[kind],
                )
                for kind in self.mro_tracker_method_kinds()
            ],
        ]:
            assert items <= all_items, (
                f"MROTrackerDatum error: {items} not tracked transitively: "
                f"{items - all_items}"
            )


@dataclass(frozen=True)
class MROTrackerData[T](MROTrackerDataMixin):
    """Full inheritance hierarchy information for a class or instance.

    This dataclass stores information about the inheritance hierarchy of a class or instance.
    It's used internally by the framework to track method registration across the inheritance
    hierarchy.
    """

    cls: type[T] = field(kw_only=True)
    self: T | None = field(kw_only=True, default=None)
    data: dict[type[Any], MROTrackerDatum[Any]] = field(kw_only=True, default_factory=dict)

    @classmethod
    def mro_tracker_datum_cls[X](
        cls: type[MROTrackerData[X]],
    ) -> type[MROTrackerDatum[X]]:
        """The MROTrackerDatum type for the given class."""
        return MROTrackerDatum[X]

    @classmethod
    def build[X](
        cls: type[MROTrackerData[X]],
        klass: type[X],
        self: X | None = None,
    ) -> MROTrackerData[X]:
        """Build a MROTrackerData object for a given class and instance."""
        data: dict[type[Any], MROTrackerDatum[Any]] = {}
        for base in klass.mro():
            base_datum = cls.mro_tracker_lookup(
                obj=base,
                attr_ty=MROTrackerDatum,
                strict=True,
            )
            if base in data:
                assert base_datum == data[base], (
                    f"MROTrackerData error: {base_datum} != {data[base]}"
                )
            else:
                data[base] = base_datum
        return cls(cls=klass, self=self, data=data)

    def compute_extra(self) -> MROTrackerData[T]:
        """Run the locally defined methods that compute extra data and return a new MROTrackerData with the computed data."""
        return self.__class__(
            cls=self.cls,
            self=self.self,
            data={base: datum.compute_extra(instance=self.self) for base, datum in self.data.items()},
        )

    def __post_init__(self) -> None:
        """Validate tracking data consistency."""
        assert self.cls is not None, "MROTrackerData error: cls is None"
        assert self.data[self.cls] is not None, "MROTrackerData error: data[self.cls] is None"
        assert self.data[self.cls].cls == self.cls, (
            "MROTrackerData error: data[self.cls].cls != self.cls:"
            f"{self.data[self.cls].cls} != {self.cls}"
        )

        if self.self is not None:
            assert isinstance(self.self, self.cls), (
                "MROTrackerData error: self is not an instance of cls:"
                f"{self.self} is not an instance of {self.cls}"
            )

        for base in self.cls.mro():
            assert base in self.data, \
                f"MROTrackerData error: {base} not in data: {self.data.keys()}"
