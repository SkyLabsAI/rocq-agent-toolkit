"""Property-based tests for TraceCursorSpanAttrs (de)serialization."""

from __future__ import annotations

import json
from glob import glob
from pathlib import Path

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st
from hypothesis_jsonschema import from_schema
from observability import model_as_otel_attrs, model_from_otel_attrs
from rocq_pipeline.trace_cursor import (
    SCHEMA_FILENAME,
    LocationInfo,
    TraceCursorSpanAttrs,
)

SCHEMAS_DIR = Path(__file__).parent / "schemas"

# ---------------------------------------------------------------------------
# Strategies
# ---------------------------------------------------------------------------

_location_info_st = st.builds(
    LocationInfo,
    id=st.text(min_size=1, max_size=40),
    goal=st.none() | st.text(max_size=200),
)

_trace_attrs_st = st.builds(
    TraceCursorSpanAttrs,
    args=st.text(max_size=100)
    | st.integers()
    | st.dictionaries(
        st.text(alphabet=st.characters(exclude_characters=["."]), max_size=20),
        st.text(max_size=50),
        max_size=5,
    ),
    action=st.none() | st.text(max_size=50),
    before=st.none() | _location_info_st,
    after=st.none() | _location_info_st,
    error=st.none() | st.booleans(),
    result=st.none() | st.text(max_size=100) | st.integers(),
    result_type=st.none() | st.text(max_size=80),
)


# ---------------------------------------------------------------------------
# Round-trip property test
# ---------------------------------------------------------------------------


@given(attrs=_trace_attrs_st)
@settings(max_examples=200)
def test_round_trip(attrs: TraceCursorSpanAttrs) -> None:
    """serialize -> deserialize must recover the original model."""
    prefix = "RocqCursor.test"
    serialized = model_as_otel_attrs(attrs, prefix=prefix)
    deserialized = model_from_otel_attrs(
        serialized, TraceCursorSpanAttrs, prefix=prefix
    )
    assert deserialized == attrs


# ---------------------------------------------------------------------------
# Schema drift detection
# ---------------------------------------------------------------------------


def test_schema_unchanged() -> None:
    """Fail loudly when the model schema changes without a version bump."""
    current = json.dumps(
        TraceCursorSpanAttrs.model_json_schema(), sort_keys=True, indent=2
    )
    persisted = (SCHEMAS_DIR / SCHEMA_FILENAME).read_text()
    expected = json.dumps(json.loads(persisted), sort_keys=True, indent=2)
    assert current == expected, (
        "Schema changed! Bump SCHEMA_VERSION and persist the new schema."
    )


# ---------------------------------------------------------------------------
# Forwards compatibility: old schemas must validate under the current model
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "schema_file",
    sorted(glob(str(SCHEMAS_DIR / "TraceCursorSpanAttrs.v*.json"))),
    ids=lambda p: Path(p).stem,
)
def test_forwards_compat(schema_file: str) -> None:
    """Data generated from any persisted schema version must be accepted by
    the current model (thanks to ``extra='ignore'``)."""
    old_schema = json.loads(Path(schema_file).read_text())

    @given(from_schema(old_schema))
    @settings(max_examples=100)
    def check(value: dict) -> None:
        TraceCursorSpanAttrs.model_validate(value)

    check()
