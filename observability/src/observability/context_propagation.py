"""
Helpers for propagating observability context across threads and async boundaries.

Why this exists:
- OpenTelemetry stores the "current span" in contextvars.
- Our structured logging context also uses a ContextVar.
- Python thread pools (ThreadPoolExecutor) do NOT automatically propagate
  contextvars into worker threads.

These helpers let callers capture the current execution context and re-bind it
inside worker threads so spans stay parented correctly and logs keep correlation
fields (e.g. run_id/task_id).
"""

from __future__ import annotations

from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Any

from opentelemetry import context as otel_context

from .logging.core import bind_log_context, get_log_context


@dataclass(frozen=True)
class ExecutionContext:
    """Snapshot of execution-local observability context."""

    otel: otel_context.Context
    log: dict[str, Any]


def capture_execution_context() -> ExecutionContext:
    """Capture the current OpenTelemetry + logging context as a snapshot."""

    return ExecutionContext(otel=otel_context.get_current(), log=get_log_context())


@contextmanager
def bind_execution_context(ctx: ExecutionContext) -> Iterator[None]:
    """Bind an ExecutionContext for the duration of this context manager."""

    token = otel_context.attach(ctx.otel)
    try:
        with bind_log_context(ctx.log):
            yield
    finally:
        otel_context.detach(token)


