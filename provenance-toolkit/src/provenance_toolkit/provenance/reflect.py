"""Reflect provenance - automatically includes annotated class/instance data members.

This module provides a mixin that automatically collects annotated class/instance
data members into provenance dictionaries. Fields are marked using Annotated types
with the Data annotation.

cf. __init__.py for more details."""

from __future__ import annotations

import inspect
import json
import logging
import types
from collections.abc import Callable
from dataclasses import dataclass
from typing import Annotated, Any, Literal, NewType, TypeVar, Union, get_args, get_origin, get_type_hints, override

from ..proto import (
    ProvenanceT,
    WithClassProvenance,
    WithInstanceProvenance,
    WithProvenance,
)

logger = logging.getLogger(__name__)

T = TypeVar("T")


@dataclass(frozen=True)
class TransformData:
    """Frozen dataclass that wraps a transform callable.

    Used to identify transform metadata in Annotated hints.
    """

    func: Callable[[Any], Any]


def _is_subtype(sub: Any, parent: Any) -> bool:
    """Recursively checks if 'sub' type is compatible with 'parent' type hint.

    Args:
        sub: The subtype to check
        parent: The parent type hint to check against

    Returns:
        True if sub is compatible with parent, False otherwise
    """
    # Strip Annotated wrappers to get the underlying type
    origin_sub = get_origin(sub) or sub
    origin_parent = get_origin(parent) or parent

    # Handle Annotated types by extracting the underlying type
    if origin_sub is Annotated:
        args = get_args(sub)
        if args:
            return _is_subtype(args[0], parent)
    if origin_parent is Annotated:
        args = get_args(parent)
        if args:
            return _is_subtype(sub, args[0])

    # Handle 'Any'
    if origin_parent is Any:
        return True

    # Handle Literal types - check if parent type matches the type of literal values
    if origin_sub is Literal:
        literal_args = get_args(sub)
        if literal_args:
            # Get the type of the first literal value as representative
            literal_type = type(literal_args[0])
            return _is_subtype(literal_type, parent)

    # Handle NewType - check the underlying type
    if isinstance(origin_sub, NewType):
        # NewType doesn't have get_origin, but we can check its __supertype__
        if hasattr(origin_sub, "__supertype__"):
            return _is_subtype(origin_sub.__supertype__, parent)

    # If the input type is a Union, ALL possible types must be compatible with parent
    if origin_sub in (types.UnionType, Union):
        return all(_is_subtype(arg, parent) for arg in get_args(sub))

    # If the parent is a Union, the sub must match AT LEAST ONE member
    if origin_parent in (types.UnionType, Union):
        return any(_is_subtype(sub, arg) for arg in get_args(parent))

    try:
        # origin_sub and origin_parent are already the base types (or original values)
        # after the initial get_origin() calls, so we can use them directly
        if isinstance(origin_sub, type) and isinstance(origin_parent, type):
            return issubclass(origin_sub, origin_parent)
    except TypeError:
        return origin_sub == origin_parent

    return origin_sub == origin_parent


def _accepts_type(fn: Callable[[Any], Any], expected_type: Any) -> bool:
    """Predicate: True if calling fn with a value of expected_type is type-safe.

    Checks both structural compatibility (can bind the argument) and type hint
    compatibility (the parameter's type hint accepts expected_type).

    Args:
        fn: The callable to validate
        expected_type: The expected type of the first argument

    Returns:
        True if the callable can safely accept a value of expected_type, False otherwise
    """
    try:
        sig = inspect.signature(fn)
        params = list(sig.parameters.values())
        if not params:
            return False

        first_param = params[0]

        # 1. Structural Check: Can we bind the first argument?
        # Check if the first parameter can accept a positional argument
        # (POSITIONAL_ONLY or POSITIONAL_OR_KEYWORD)
        if first_param.kind in (
            inspect.Parameter.POSITIONAL_ONLY,
            inspect.Parameter.POSITIONAL_OR_KEYWORD,
        ):
            # Check if we can bind with just this one argument (all others have defaults)
            try:
                bound = sig.bind(object())
                bound.apply_defaults()
                if not all(p in bound.arguments for p in sig.parameters):
                    return False
            except TypeError:
                return False
        elif first_param.kind == inspect.Parameter.KEYWORD_ONLY:
            # Keyword-only parameters can't be bound positionally
            return False
        # VAR_POSITIONAL (*args) and VAR_KEYWORD (**kwargs) are acceptable

        # 2. Type Hint Check: Does the first parameter's hint allow 'expected_type'?
        # Resolve forward refs with get_type_hints
        hints = get_type_hints(fn, include_extras=True)
        first_hint = hints.get(first_param.name, Any)
        return _is_subtype(expected_type, first_hint)
    except (TypeError, ValueError):
        return False


class Data[*Ts]:
    """Annotation type for marking fields to include in provenance data.

    Usage:
        # No transform
        field: Data[int] = 42

        # With transform callable
        field: Data[int, lambda x: round(x, 2)] = 3.14159
    """

    def __class_getitem__(cls, params: type | tuple[type, ...]) -> Annotated[*Ts]:
        """Handle Data[T] and Data[T, callable] patterns.

        Args:
            params: Either a single type T, or a tuple (T, callable)

        Returns:
            Annotated type with appropriate metadata

        Raises:
            TypeError: If callable signature doesn't match type T
        """
        if not isinstance(params, tuple):
            # Data[T] - no transform
            base_type = params
            # Annotated requires at least one metadata item, use empty tuple as marker
            return Annotated[base_type, ()]
        else:
            # Data[T, callable] - with transform
            if len(params) != 2:
                raise TypeError(
                    f"Data expects 1 or 2 arguments, got {len(params)}: {params}"
                )
            base_type, callable_arg = params

            # Validate callable signature matches base_type
            if not callable(callable_arg):
                raise TypeError(
                    f"Second argument to Data must be callable, got {type(callable_arg)}"
                )

            # Validate that callable signature is compatible with base_type
            if not _accepts_type(callable_arg, base_type):
                raise TypeError(
                    f"Transform callable {callable_arg} signature is not compatible "
                    f"with type {base_type}. The callable must accept at least one "
                    "parameter that can be bound with a value of the annotated type."
                )

            # Wrap callable in TransformData
            transform = TransformData(callable_arg)
            return Annotated[base_type, transform]


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

    This mixin scans class/instance annotations for fields marked with Data[...]
    and includes them in provenance computation.
    """

    @override
    @classmethod
    def compute_cls_provenance(cls) -> dict[type[WithClassProvenance], ProvenanceT]:
        result = super().compute_cls_provenance()
        data_dict = _collect_annotated_data(cls, is_class=True)
        result[WithReflectProvenance] = ReflectProvenanceData(data_dict)
        return result

    @override
    def compute_provenance(self) -> dict[type[WithInstanceProvenance], ProvenanceT]:
        result = super().compute_provenance()
        data_dict = _collect_annotated_data(
            self.__class__, is_class=False, instance=self
        )
        result[WithReflectProvenance] = ReflectProvenanceData(data_dict)
        return result

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)


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
        unwrapped = _unwrap_to_annotated(arg)
        if unwrapped is not None:
            return unwrapped

    return None


def _collect_annotated_data(
    klass: type, is_class: bool, instance: Any | None = None
) -> dict[str, Any]:
    """Collect data from fields annotated with Data[...].

    Args:
        klass: The class to scan
        is_class: Whether we're computing class provenance (True) or instance (False)
        instance: The instance object (if computing instance provenance)

    Returns:
        Dictionary mapping field names to transformed values
    """
    data_dict: dict[str, Any] = {}

    # Get all type hints with extras (to access Annotated metadata)
    hints = get_type_hints(klass, include_extras=True)

    for field_name, hint in hints.items():
        # Recursively unwrap to find Annotated type
        annotated_hint = _unwrap_to_annotated(hint)
        if annotated_hint is None:
            continue

        # Extract the base type and metadata
        args = get_args(annotated_hint)
        if not args:
            continue
        _base_type, *metadata = args

        # Check if any metadata is a TransformData instance
        # Skip empty tuple marker used for Data[T] (no transform)
        transform: TransformData | None = None
        for meta in metadata:
            if isinstance(meta, TransformData):
                transform = meta
                break
            # Empty tuple () is used as a marker for Data[T] with no transform
            # We can ignore it and proceed with no transform

        # Get the field value
        if is_class:
            # For class provenance, get from class attributes
            if hasattr(klass, field_name):
                value = getattr(klass, field_name)
            else:
                # Class annotation exists but no value assigned - use None
                value = None
        else:
            # For instance provenance, get from instance
            if instance is None:
                continue
            if hasattr(instance, field_name):
                value = getattr(instance, field_name)
            else:
                # Instance annotation exists but no value assigned - use None
                value = None

        # Apply transform
        transformed_value = _apply_transform(value, transform, field_name)
        data_dict[field_name] = transformed_value

    return data_dict


def _apply_transform(
    value: Any, transform: TransformData | None, field_name: str
) -> Any:
    """Apply transform to a value according to priority.

    Priority:
    1. Explicit transform from TransformData.func
    2. Best-effort auto-detection: if value has cls_provenance() or provenance()
    3. Identity function (return value as-is)

    Args:
        value: The value to transform
        transform: Optional TransformData instance
        field_name: Name of the field (for error messages)

    Returns:
        Transformed value
    """
    # Priority 1: Explicit transform
    if transform is not None:
        try:
            return transform.func(value)
        except (ValueError, TypeError, AttributeError) as e:
            logger.warning(
                "Transform failed for field %s: %s. Using value as-is.",
                field_name,
                e,
            )
            return value

    # Priority 2: Best-effort auto-detection
    # Check if value has cls_provenance() method
    if isinstance(value, WithClassProvenance):
        try:
            prov_dict = value.cls_provenance()
            # Extract checksum or serialize
            if prov_dict:
                # Use the joint checksum
                from ..proto.base import ProvenanceT as ProvenanceTBase

                return ProvenanceTBase.joint_checksum(prov_dict)
            return str(value)
        except (AttributeError, TypeError) as e:
            logger.debug(
                "Auto-detection via cls_provenance failed for %s: %s",
                field_name,
                e,
            )

    # Check if value has provenance() method
    if isinstance(value, WithInstanceProvenance):
        try:
            prov_dict = value.provenance()
            # Extract checksum or serialize
            if prov_dict:
                # Use the joint checksum
                from ..proto.base import ProvenanceT as ProvenanceTBase

                return ProvenanceTBase.joint_checksum(prov_dict)
            return str(value)
        except (AttributeError, TypeError) as e:
            logger.debug(
                "Auto-detection via provenance failed for %s: %s",
                field_name,
                e,
            )

    # Priority 3: Identity function (assume JSON-serializable)
    return value


# Attach Data to WithReflectProvenance so it's accessible via Provenance.Reflect.Data
WithReflectProvenance.Data = Data  # type: ignore[attr-defined]
