"""
Core observability functionality.

This module provides the fundamental building blocks for observability:
- Generic tracing decorator
- Context managers for manual instrumentation
- Metrics collection
- Structured logging

All functionality is framework-agnostic and works with any Python application.
"""

from .decorators import trace
from .context import trace_context, get_current_span
from .metrics import metrics
from psi_verifier.psi_logging import get_logger

__all__ = [
    "trace",
    "trace_context", 
    "get_current_span",
    "metrics",
    "get_logger",
] 