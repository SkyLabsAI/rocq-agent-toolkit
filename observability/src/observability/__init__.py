"""
Framework-Agnostic Observability Package (v2)

A comprehensive, production-ready observability solution that works with any Python
application. Provides distributed tracing, metrics collection, and structured logging
through a unified, framework-agnostic API using the extractor pattern.
"""

# Core API - the main interfaces everyone should use
from .tracing.decorators import (
    trace,
    trace_http,
    trace_rpc,
    trace_database,
    trace_workflow,
    trace_langchain,
)
from .tracing.context import (
    trace_context,
    get_current_span,
    add_span_event,
    set_span_attribute,
)

# gRPC interceptors for distributed tracing
# now handled by opentelemetry-instrumentation-grpc
from opentelemetry.instrumentation.grpc import aio_server_interceptor
from opentelemetry import propagate

# Logging is now integrated as a submodule
from .logging.core import (
    get_logger,
    configure_logging,
    set_global_service_name,
    set_global_event_context,
    get_global_event_context,
    configure_event_schemas,
    add_log_context,
    clear_log_context,
    get_log_context,
    is_otel_available,
)


# Configuration and setup
from .config import CoreConfig
from .tracing.config import ObservabilityConfig
from .logging.config import (
    LoggingConfig,
    WorkflowEventConfig,
    LangGraphEventConfig,
    EvaluationEventConfig,
    TrainingEventConfig,
)
from .tracing.setup import setup_observability
from .logging.setup import setup_logging

# Extractors - for advanced usage and custom extractors
from .tracing.extractors import (
    AttributeExtractor,
    HttpExtractor,
    RpcExtractor,
    DatabaseExtractor,
    WorkflowExtractor,
    LangChainExtractor,
    CustomExtractor,
)

# Specialized extractors
from .tracing.extractors.custom import BusinessOperationExtractor, MLOperationExtractor

__version__ = "2.0.0"

__all__ = [
    # Core API (recommended for most users)
    "trace",
    "trace_context",
    "get_current_span",
    "add_span_event",
    "set_span_attribute",
    "get_logger",
    # Setup and configuration
    "ObservabilityConfig",
    "CoreConfig",
    "LoggingConfig",
    "setup_observability",
    "configure_logging",
    "setup_logging",
    "set_global_service_name",
    "set_global_event_context",
    "get_global_event_context",
    "configure_event_schemas",
    "add_log_context",
    "clear_log_context",
    "get_log_context",
    "is_otel_available",
    # Convenience decorators
    "trace_http",
    "trace_rpc",
    "trace_database",
    "trace_workflow",
    "trace_langchain",
    # gRPC interceptors are now handled by the official library
    "aio_server_interceptor",
    # OTel Passthrough
    "propagate",
    # Extractors (for advanced usage)
    "AttributeExtractor",
    "HttpExtractor",
    "RpcExtractor",
    "DatabaseExtractor",
    "WorkflowExtractor",
    "LangChainExtractor",
    "CustomExtractor",
    "BusinessOperationExtractor",
    "MLOperationExtractor",
    # Configuration
    "WorkflowEventConfig",
    "LangGraphEventConfig",
    "EvaluationEventConfig",
    "TrainingEventConfig",
]
