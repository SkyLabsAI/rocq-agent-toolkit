"""
Structured Logging Package

Provides structured logging with OpenTelemetry integration, OTLP export,
and event-based schema filtering.
"""

# Configuration classes
from .config import (
    EvaluationEventConfig,
    LangGraphEventConfig,
    LoggingConfig,
    TrainingEventConfig,
    WorkflowEventConfig,
)

# Core logging functionality
from .core import (
    StructuredLogger,
    add_log_context,
    clear_log_context,
    configure_event_schemas,
    configure_logging,
    get_global_event_context,
    get_log_context,
    get_logger,
    is_otel_available,
    set_global_event_context,
    set_global_service_name,
)

# Setup with OTLP export
from .setup import FixedLoggingHandler, setup_logging

__all__ = [
    # Configuration
    "LoggingConfig",
    "EventLogConfig",
    "TrainingEventConfig",
    "WorkflowEventConfig",
    "EvaluationEventConfig",
    "LangGraphEventConfig",
    # Core functionality
    "StructuredLogger",
    "get_logger",
    "configure_logging",
    "set_global_service_name",
    "set_global_event_context",
    "get_global_event_context",
    "configure_event_schemas",
    "add_log_context",
    "clear_log_context",
    "get_log_context",
    "is_otel_available",
    # Setup
    "setup_logging",
    "FixedLoggingHandler",
]
