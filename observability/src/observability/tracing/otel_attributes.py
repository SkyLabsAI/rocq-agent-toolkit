"""Typed (de)serialization of pydantic models to/from flat OTel span attributes.

Adapts the approach of pydantic/logfire's ``prepare_otlp_attribute``:
- primitive types (``int``, ``str``, ``bool``, ``float``) pass through
- top-level sequences are retained
- everything else is JSON-encoded

On top of that, nested pydantic models are flattened into dot-separated keys so
individual fields are queryable in backends like Tempo / Grafana.
"""

from __future__ import annotations

import json
from collections.abc import Sequence
from typing import Any, TypeGuard

from opentelemetry.trace import Span
from pydantic import BaseModel

from observability import get_logger

type OtelAttrPrimitive = str | int | float | bool
# Note: opentelemetry sequences are homogeneous
type OtelAttrValue = (
    OtelAttrPrimitive | Sequence[str] | Sequence[int] | Sequence[float] | Sequence[bool]
)


# Note: [type]s cannot be used for isinstance checks
def is_OtelAttrPrimitive(value: Any) -> TypeGuard[OtelAttrPrimitive]:
    return isinstance(value, (str, int, float, bool))


def set_otel_attrs_on_span(
    span: Span,
    data: BaseModel | dict[str, Any],
    *,
    prefix: str = "",
) -> None:
    """Flatten *data* and set all resulting attributes on *span*.

    *data* may be a pydantic ``BaseModel`` (dumped to JSON-safe dict first) or
    a plain ``dict``.
    """
    if isinstance(data, BaseModel):
        data = data.model_dump(mode="json", exclude_none=True)

    serialized_attrs = as_otel_attrs(data, prefix=prefix)

    if not span.is_recording():
        get_logger(__name__).info(
            "set_otel_attrs_on_span.not_recording",
            serialized_attrs,
        )
        return

    for key, value in serialized_attrs.items():
        span.set_attribute(key, value)


def as_otel_attr_value(value: Any) -> OtelAttrValue:
    """Convert an arbitrary Python value to an OTel-compatible attribute value.

    Primitives pass through.  Sequences are retained **only** when every element
    shares the exact same primitive type (OTel arrays must be homogeneous);
    otherwise the whole value is JSON-encoded.
    """
    if is_OtelAttrPrimitive(value):
        return value
    if isinstance(value, Sequence):
        return _as_otel_sequence(value)
    return json.dumps(value, default=str)


def _as_otel_sequence(seq: Sequence[Any]) -> OtelAttrValue:
    """Return *seq* as a homogeneous OTel array, or JSON-encode it.

    Uses ``type(x) is ...`` (not ``isinstance``) so that ``bool`` and ``int``
    are kept distinct — OTel treats them as separate element types.
    """
    if not seq or not is_OtelAttrPrimitive(seq[0]):
        return json.dumps(seq, default=str)

    primitive_elem_type = type(seq[0])
    if all(type(x) is primitive_elem_type for x in seq):
        return list(seq)

    return json.dumps(seq, default=str)


def as_otel_attrs(
    data: dict[str, Any], *, prefix: str = ""
) -> dict[str, OtelAttrValue]:
    """Flatten a nested dict into dot-separated OTel span attributes.

    >>> as_otel_attrs({"name": "x", "inner": {"id": "abc"}})
    {'name': 'x', 'inner.id': 'abc'}
    """
    out: dict[str, OtelAttrValue] = {}
    _otel_attrs_flatten(data, prefix, out)
    return out


def from_otel_attrs(
    attrs: dict[str, OtelAttrValue], *, prefix: str = ""
) -> dict[str, Any]:
    """Reverse dot-separated OTel attributes back into a nested dict.

    If *prefix* is given, only keys starting with ``prefix.`` are considered
    and the prefix is stripped before unflattening.
    """
    if prefix:
        dot_prefix = f"{prefix}."
        attrs = {
            k[len(dot_prefix) :]: v
            for k, v in attrs.items()
            if k.startswith(dot_prefix)
        }
    return _otel_attrs_unflatten(attrs)


def model_as_otel_attrs(
    model: BaseModel, *, prefix: str = ""
) -> dict[str, OtelAttrValue]:
    """Flatten a pydantic model into dot-separated OTel span attributes.

    >>> from pydantic import BaseModel
    >>> class Inner(BaseModel):
    ...     id: str
    >>> class Outer(BaseModel):
    ...     name: str
    ...     inner: Inner
    >>> model_as_otel_attrs(Outer(name="x", inner=Inner(id="abc")))
    {'name': 'x', 'inner.id': 'abc'}
    """
    dumped = model.model_dump(mode="json", exclude_none=True)
    return as_otel_attrs(dumped, prefix=prefix)


def model_from_otel_attrs[T: BaseModel](
    attrs: dict[str, OtelAttrValue],
    cls: type[T],
    *,
    prefix: str = "",
) -> T:
    """Unflatten dot-separated OTel attributes and validate as *cls*.

    Extra keys that do not map to fields on *cls* are silently ignored, so
    callers can pass the full span-attribute dict without pre-filtering.
    """
    nested = from_otel_attrs(attrs, prefix=prefix)
    projected = {k: v for k, v in nested.items() if k in cls.model_fields}
    return cls.model_validate(projected)


def _otel_attrs_flatten(
    data: dict[str, Any],
    prefix: str,
    out: dict[str, OtelAttrValue],
) -> None:
    """Recursively flatten *data* into dot-separated keys in *out*."""
    for key, value in data.items():
        if isinstance(key, str) and "." in key:
            raise ValueError(f"OTel flatten dict keys must not contain '.': {key!r}")
        full_key = f"{prefix}.{key}" if prefix else key
        if isinstance(value, dict):
            _otel_attrs_flatten(value, full_key, out)
        else:
            out[full_key] = as_otel_attr_value(value)


def _otel_attrs_unflatten(attrs: dict[str, Any]) -> dict[str, Any]:
    """Reverse dot-separated keys back into a nested dict."""
    result: dict[str, Any] = {}
    for key, value in attrs.items():
        parts = key.split(".")
        current = result
        for part in parts[:-1]:
            current = current.setdefault(part, {})
        current[parts[-1]] = _try_json_loads(value)
    return result


# TODO: cleanup by using centralized (de)serialization logic from `rocq-agent-toolkit-utils`
def _try_json_loads(value: Any) -> Any:
    """If *value* is a JSON-encoded string, decode it; otherwise return as-is."""
    if not isinstance(value, str):
        return value
    # Fast-reject: only try to parse strings that look like JSON structures
    if value and value[0] in ("{", "[", '"'):
        try:
            return json.loads(value)
        except (json.JSONDecodeError, ValueError):
            pass
    return value
