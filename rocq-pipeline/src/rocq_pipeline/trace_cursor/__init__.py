"""trace_cursor — structured tracing for RocqCursor operations."""

from .cursor import TracingCursor
from .telemetry.instrumentation import InstrumentRocqCursor
from .telemetry.schema import (
    SCHEMA_FILENAME,
    SCHEMA_VERSION,
    InstrumentRocqCursorSpanAttrs,
    LocationInfo,
    persist_schema,
)

__all__ = [
    "SCHEMA_FILENAME",
    "SCHEMA_VERSION",
    "LocationInfo",
    "InstrumentRocqCursorSpanAttrs",
    "InstrumentRocqCursor",
    "TracingCursor",
    "persist_schema",
]
