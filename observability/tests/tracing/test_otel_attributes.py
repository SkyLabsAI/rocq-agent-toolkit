"""Tests for OTel attribute flattening."""

import pytest
from observability.tracing.otel_attributes import as_otel_attrs


def test_as_otel_attrs_rejects_dot_in_key() -> None:
    with pytest.raises(ValueError, match=r"must not contain"):
        as_otel_attrs({"a.b": 1})


def test_as_otel_attrs_rejects_dot_in_nested_key() -> None:
    with pytest.raises(ValueError, match=r"must not contain"):
        as_otel_attrs({"outer": {"in.ner": 2}})
