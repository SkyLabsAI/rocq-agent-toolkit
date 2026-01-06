"""Reflect provenance - automatically includes annotated class/instance data members.

This module provides a mixin that automatically collects annotated class/instance
data members into provenance dictionaries. Fields are marked using Annotated types
with the Field class.

cf. __init__.py for more details."""

from __future__ import annotations

import json
import logging
from collections.abc import Callable
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

    def __init__(self, data: dict[str, Any]) -> None:
        self._data = data

    @property
    def data(self) -> dict[str, Any]:
        """Get the data dictionary."""
        return self._data

    def __eq__(self, other: Any) -> Any:
        super_eq = super().__eq__(other)
        if super_eq is NotImplemented:
            return NotImplemented
        return self._data == other._data

    @override
    def is_cls_provenance(self) -> bool:
        return True

    @override
    def is_instance_provenance(self) -> bool:
        return True

    @override
    def stable_serialize(self) -> str:
        """Serialize data to a stable JSON string."""
        return json.dumps(self._data, sort_keys=True, ensure_ascii=False)


class WithReflectProvenance(WithProvenance):
    """Protocol for types that automatically include annotated data members in provenance.

    This mixin scans class/instance annotations for marked fields and includes them in
    provenance computation. The following annotations can be used:
    - Annotated[T, Field]: value of type T; use a default strategy to reflect it
    - Annotated[T, Field(transform=...)]: value of type T; use a custom transform to reflect it
    """

    @dataclass(frozen=True)
    class Field[T]:
        """Frozen dataclass used to mark reflection targets in Annotated hints."""

        transform: Callable[[T], Any] | None = field(kw_only=True, default=None)

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)

    @override
    @classmethod
    def compute_cls_provenance(cls) -> dict[type[WithClassProvenance], ProvenanceT]:
        result = super().compute_cls_provenance()
        data_dict = WithReflectProvenance._collect_annotated_data(cls, instance=None)
        result[WithReflectProvenance] = ReflectProvenanceData(data_dict)
        return result

    @override
    def compute_provenance(self) -> dict[type[WithInstanceProvenance], ProvenanceT]:
        result = super().compute_provenance()
        data_dict = WithReflectProvenance._collect_annotated_data(
            type(self), instance=self
        )
        result[WithReflectProvenance] = ReflectProvenanceData(data_dict)
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

            reflect: WithReflectProvenance.Field | None = None
            for meta in metadata:
                if isinstance(meta, WithReflectProvenance.Field):
                    reflect = meta
                    break
                elif meta is WithReflectProvenance.Field or (
                    isinstance(meta, type) and meta.__name__ == "Field"
                ):
                    reflect = WithReflectProvenance.Field(transform=None)
                    break
            if reflect is None:
                continue

            # Get the field value; use None for uninitialized fields
            if instance is None:
                # For class provenance, only include fields that exist at class level
                if hasattr(klass, field_name):
                    value = getattr(klass, field_name)
                else:
                    # Skip instance-only fields in class provenance
                    continue
            else:
                if hasattr(instance, field_name):
                    value = getattr(instance, field_name)
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
        value: T,
        reflect: WithReflectProvenance.Field[T],
        field_name: str,
        is_cls_provenance: bool,
    ) -> Any:
        """Reflect field_value using reflect, or a default policy.

        Priority:
        1. Explicit reflect using reflect.func
        2. Default:
           a. Best-effort auto-detection: if value has cls_provenance() or provenance()
           b. Identity function (return value as-is)

        Args:
            value: The value to transform
            reflect: Field instance
            field_name: Name of the field (for error messages)
            is_cls_provenance: Whether this is for class provenance (True) or instance (False)

        Returns:
            Reflected field value
        """
        # Priority 1: Explicit transform
        if reflect.transform is not None:
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
        if is_cls_provenance and (
            isinstance(value, WithClassProvenance)
            or isinstance(value, type)
            and issubclass(value, WithClassProvenance)
        ):
            return value.cls_provenance()
        elif not is_cls_provenance and isinstance(value, WithInstanceProvenance):
            return value.provenance()
        else:
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
