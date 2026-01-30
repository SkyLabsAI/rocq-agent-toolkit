"""Reflect provenance - automatically includes annotated class/instance data members.

This module provides a mixin that automatically collects annotated class/instance
data members into provenance dictionaries. Fields are marked using Annotated types
with the Field class.

cf. __init__.py for more details."""

from __future__ import annotations

import inspect
import json
import logging
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, field
from typing import (
    Annotated,
    Any,
    get_args,
    get_origin,
    get_type_hints,
    override,
)

from ..proto import (
    ProvenanceT,
    WithClassProvenance,
    WithInstanceProvenance,
    WithProvenance,
)

logger = logging.getLogger(__name__)


class ReflectProvenanceData(ProvenanceT):
    """Provenance data that holds a dictionary of included field data."""

    def __init__(self, data: dict[str, Any], is_cls_provenance: bool = False) -> None:
        self._data = data
        self._is_cls_provenance = is_cls_provenance

    @property
    def data(self) -> dict[str, Any]:
        """Get the data dictionary."""
        return self._data

    def __eq__(self, other: Any) -> Any:
        super_eq = super().__eq__(other)
        if super_eq is NotImplemented:
            return NotImplemented
        elif not super_eq:
            return False
        return (
            self._data == other._data
            and self._is_cls_provenance == other._is_cls_provenance
        )

    @override
    def is_cls_provenance(self) -> bool:
        return self._is_cls_provenance

    @override
    def is_instance_provenance(self) -> bool:
        return not self._is_cls_provenance

    @override
    def stable_serialize(self) -> str:
        """Serialize data to a stable JSON string.

        Provenance dictionaries (dicts with type keys) are converted to dicts with
        __qualname__ string keys, following the pattern used in cls_provenance_json.
        """
        serializable_data = self._convert_to_json_serializable(self._data)
        return json.dumps(serializable_data, sort_keys=True, ensure_ascii=False)

    def _convert_to_json_serializable(self, value: Any) -> Any:
        """Convert value to JSON-serializable format, handling provenance dictionaries.

        Uses generic_map pattern to recursively process mappings and sequences.
        """
        return ReflectProvenanceData._generic_map(
            value_func=self._convert_value,
            key_func=ReflectProvenanceData._convert_key,
            data=value,
        )

    def _convert_value(self, value: Any) -> Any:
        """Convert value to JSON-serializable format.

        If value is a ProvenanceT instance, use stable_serialize().
        If value has instance provenance, get its provenance and recursively process it.
        If value is container-like, recursively process it.
        Otherwise, return as-is.
        """
        if isinstance(value, ProvenanceT):
            return value.stable_serialize()
        elif isinstance(value, WithClassProvenance) or isinstance(
            value, WithInstanceProvenance
        ):
            if self.is_cls_provenance() and isinstance(value, WithClassProvenance):
                return value.cls_provenance_json()
            elif self.is_instance_provenance() and isinstance(
                value, WithInstanceProvenance
            ):
                return value.provenance_json()
            else:
                if self.is_cls_provenance():
                    prov_kind = "class"
                    base_type_name = WithClassProvenance.__qualname__
                else:
                    prov_kind = "instance"
                    base_type_name = WithInstanceProvenance.__qualname__
                raise ValueError(
                    f"Invalid value for {prov_kind} provenance: "
                    f"{type(value).__qualname__} does not derive "
                    f"from {base_type_name}; value={value}"
                )
        elif self._is_container_like(value):
            return self._convert_to_json_serializable(value)
        return value

    @staticmethod
    def _convert_key(key: Any) -> Any:
        """Convert key to JSON-serializable format.

        If key supports < comparison, leave as-is. Otherwise, use __qualname__
        if it's a type, or str() otherwise.
        """
        if ReflectProvenanceData._key_supports_less_than(key):
            return key
        if isinstance(key, type):
            return key.__qualname__
        return str(key)

    @staticmethod
    def _key_supports_less_than(key: Any) -> bool:
        """Check if key supports less-than comparison (for json.dumps sort_keys=True)."""
        try:
            _ = key < key
            return True
        except TypeError:
            return False

    @staticmethod
    def _is_container_like(value: Any) -> bool:
        """Check if value is a container-like object (Mapping or Sequence)."""
        return not isinstance(value, (str, bytes)) and (
            isinstance(value, Mapping) or isinstance(value, Sequence)
        )

    @staticmethod
    def _generic_map(
        *,
        value_func: Callable[[Any], Any],
        key_func: Callable[[Any], Any] | None,
        data: Any,
    ) -> Any:
        """Recursively apply 'value_func' to every leaf element in a Mapping or Sequence.

        Args:
            value_func: Function to apply to values (and leaf nodes)
            key_func: Optional function to apply to keys in mappings.
            data: The data structure to process

        Returns:
            Transformed data structure with the same shape
        """
        match data:
            # Check for strings first to avoid treating them as sequences
            case str() | bytes():
                return value_func(data)

            # Handle Mappings (dict-like)
            case Mapping():
                if key_func is not None:
                    return {
                        key_func(k): ReflectProvenanceData._generic_map(
                            value_func=value_func, key_func=key_func, data=v
                        )
                        for k, v in data.items()
                    }
                else:
                    return {
                        k: ReflectProvenanceData._generic_map(
                            value_func=value_func, key_func=key_func, data=v
                        )
                        for k, v in data.items()
                    }

            # Handle Sequences (list-like)
            case Sequence():
                return [
                    ReflectProvenanceData._generic_map(
                        value_func=value_func, key_func=key_func, data=item
                    )
                    for item in data
                ]

            # Leaf node / Base case
            case _:
                return value_func(data)


class WithReflectProvenance(WithProvenance):
    """Protocol for types that automatically reflect code info based on annotations.

    For now we only support annotations on data members.

    This mixin scans class/instance annotations for marked fields and includes them in
    provenance computation. The following annotations can be used:
    - Annotated[T, Field]: value of type T; use a default strategy to reflect it
    - Annotated[T, Field(transform=...)]: value of type T; use a custom transform to
      reflect it
    - Annotated[Callable, CallableField]: callable; extract source code with inspect.getsource
    """

    @dataclass(frozen=True)
    class Field[T]:
        """Frozen dataclass used to mark reflection targets in Annotated hints."""

        transform: Callable[[T], Any] | None = field(kw_only=True, default=None)

    @dataclass(frozen=True)
    class CallableField[**P, T](Field[Callable[P, T]]):
        """Field for callables that extracts source code using inspect.getsource.

        Derives from Field with a fixed transform that uses inspect.getsource,
        logging a warning if inspect.getsource raises fails.
        """

        def __post_init__(self) -> None:
            """Initialize the transform function that extracts source code."""

            def extract_source(callable_obj: Any) -> str:
                """Extract source code from a callable using inspect.getsource."""
                if not callable(callable_obj):
                    raise TypeError(
                        f"Expected callable object, got {type(callable_obj).__name__}: "
                        + repr(callable_obj)
                    )
                try:
                    return inspect.getsource(callable_obj)
                except Exception as e:
                    logger.warning(
                        "Failed to extract source for callable %s (using placeholder): %s.",
                        callable_obj,
                        e,
                    )
                    return "<callable>"

            object.__setattr__(self, "transform", extract_source)

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)

    @override
    @classmethod
    def compute_cls_provenance(cls) -> dict[type, ProvenanceT]:
        result = super().compute_cls_provenance()
        data_dict = WithReflectProvenance._collect_annotated_data(cls, instance=None)
        result[WithReflectProvenance] = ReflectProvenanceData(
            data_dict, is_cls_provenance=True
        )
        return result

    @override
    def compute_provenance(self) -> dict[type, ProvenanceT]:
        result = super().compute_provenance()
        data_dict = WithReflectProvenance._collect_annotated_data(
            type(self), instance=self
        )
        result[WithReflectProvenance] = ReflectProvenanceData(
            data_dict, is_cls_provenance=False
        )
        return result

    @staticmethod
    def _collect_annotated_data[SELF: WithReflectProvenance](
        klass: type[SELF], instance: SELF | None = None
    ) -> dict[str, Any]:
        """Collect data from fields annotated with Field.

        Args:
            klass: subtype of WithReflectProvenance
            instance: instance of klass (None for class provenance)

        Returns:
            Dictionary mapping field names to transformed values
        """
        if instance is not None:
            assert isinstance(instance, klass)

        data_dict: dict[str, Any] = {}

        # Get all type hints with extras (to access Annotated metadata)
        for field_name, hint in get_type_hints(klass, include_extras=True).items():
            # Recursively unwrap to find Annotated type
            annotated_hint = WithReflectProvenance._unwrap_to_annotated(hint)
            if annotated_hint is None:
                continue

            # Extract the base type and metadata
            args = get_args(annotated_hint)
            if not args:
                continue
            metadata = list(args[1:]) if len(args) > 1 else []

            reflect: WithReflectProvenance.Field[Any] | None = None
            for meta in metadata:
                if isinstance(meta, WithReflectProvenance.Field):
                    # This includes CallableField since it inherits from Field
                    reflect = meta
                    break
                elif meta is WithReflectProvenance.Field or (
                    isinstance(meta, type)
                    and meta.__qualname__ == "WithReflectProvenance.Field"
                ):
                    reflect = WithReflectProvenance.Field(transform=None)
                    break
                elif meta is WithReflectProvenance.CallableField or (
                    isinstance(meta, type)
                    and meta.__qualname__ == "WithReflectProvenance.CallableField"
                ):
                    reflect = WithReflectProvenance.CallableField()
                    break
            if reflect is None:
                continue

            # Get the field value; use None for uninitialized fields
            obj = klass if instance is None else instance
            if hasattr(obj, field_name):
                value = getattr(obj, field_name)
            else:
                value = None

            data_dict[field_name] = WithReflectProvenance._reflect_field(
                value,
                reflect,
                field_name,
                is_cls_provenance=instance is None,
            )

        return data_dict

    @staticmethod
    def _reflect_field[T](
        value: T | None,
        reflect: WithReflectProvenance.Field[T],
        field_name: str,
        is_cls_provenance: bool,
    ) -> Any:
        """Reflect field_value using reflect, or a default policy.

        Priority:
        1. Explicit reflect using reflect.transform
        2. Default:
           a. Best-effort auto-detection: if value has cls_provenance() or provenance()
           b. For container-like values, recursively process using _generic_map
           c. Identity function (return value as-is)

        Args:
            value: The value to transform
            reflect: Field instance
            field_name: Name of the field (for error messages)
            is_cls_provenance: True iff class provenance, else instance provenance

        Returns:
            Reflected field value
        """
        # Priority 1: Explicit transform
        if reflect.transform is not None and value is not None:
            try:
                return reflect.transform(value)
            except (ValueError, TypeError, AttributeError) as e:
                logger.warning(
                    "Transform failed for field %s: %s. Using value as-is.",
                    field_name,
                    e,
                )
                return value

        # Priority 2: Best-effort auto-detection
        # For instances with provenance, always use instance provenance (even for class variables)
        # because the instance has the actual data
        if isinstance(value, WithInstanceProvenance):
            return value.provenance()
        elif is_cls_provenance and (
            isinstance(value, type) and issubclass(value, WithClassProvenance)
        ):
            return value.cls_provenance()
        elif ReflectProvenanceData._is_container_like(value):
            # For container-like values, recursively process using _generic_map
            # This handles cases like list[tuple[float, T]] where T has provenance
            return ReflectProvenanceData._generic_map(
                value_func=lambda v: WithReflectProvenance._reflect_field_value(
                    v, is_cls_provenance
                ),
                key_func=None,
                data=value,
            )
        else:
            return value

    @staticmethod
    def _reflect_field_value(value: Any, is_cls_provenance: bool) -> Any:
        """Helper: process values in container-like structures.

        This applies the same logic as _reflect_field but for individual values within
        containers, handling objects with provenance recursively.

        Args:
            value: The value to process
            is_cls_provenance: True iff class provenance, else instance provenance
        """
        # For instances with provenance, always use instance provenance (even for class variables)
        # because the instance has the actual data
        if isinstance(value, WithInstanceProvenance):
            return value.provenance()
        elif is_cls_provenance and (
            isinstance(value, type) and issubclass(value, WithClassProvenance)
        ):
            return value.cls_provenance()
        # For other values, return as-is (they'll be processed by _generic_map
        # if container-like)
        return value

    @staticmethod
    def _unwrap_to_annotated(hint: Any) -> Any | None:
        """Recursively unwrap type annotations to find an Annotated type.

        Handles wrapper types like Final, ClassVar, etc. that might wrap Annotated.

        Args:
            hint: The type hint to unwrap

        Returns:
            The Annotated type if found, None otherwise
        """
        origin = get_origin(hint)

        # If it's already Annotated, return it
        if origin is Annotated:
            return hint

        # If it's not a generic type, it can't be Annotated
        if origin is None:
            return None

        # Recursively check the arguments
        args = get_args(hint)
        if not args:
            return None

        # Check each argument (for cases like Union, etc.)
        # But typically wrapper types have a single argument
        for arg in args:
            unwrapped = WithReflectProvenance._unwrap_to_annotated(arg)
            if unwrapped is not None:
                return unwrapped

        return None
