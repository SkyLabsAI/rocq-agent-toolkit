"""Automatic instrumentation of RocqCursor APIs with span-based telemetry.

Note: cf. the rocq_pipeline.trace_cursor.telemetry for more details, including overrides.
"""

from __future__ import annotations

from .telemetry.instrumentation import InstrumentRocqCursor


class TracingCursor(InstrumentRocqCursor):
    """Instrument all interfaces of RocqCursor using opentelemetry spans."""

    pass
