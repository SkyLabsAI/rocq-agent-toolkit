"""Automatic instrumentation of span-based telemetry for RocqCursor, using stable pydantic schemas."""

from . import instrumentation, schema

__all__ = [
    "instrumentation",
    "schema",
]
