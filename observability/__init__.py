"""
Framework-Agnostic Observability Package

A comprehensive, production-ready observability solution that works with any Python application.
Provides distributed tracing, metrics collection, and structured logging through a unified,
framework-agnostic API using the extractor pattern.

"""

# Core API - the main interfaces everyone should use
from .core.decorators import trace, trace_http, trace_rpc, trace_database, trace_workflow, trace_langchain
from .core.context import trace_context, get_current_span, add_span_event, set_span_attribute
from .core.metrics import metrics, set_service_name

from opentelemetry import propagate

# Logging is now a separate package (can be used independently)
from psi_verifier.psi_logging import (
    get_logger,
    setup_logging,
    configure_logging,
    set_global_service_name,
    set_global_event_context,
    get_global_event_context,
    configure_event_schemas,
    add_log_context,
    clear_log_context,
    get_log_context,
    log_operation_start,
    log_operation_success,
    log_operation_error,
    log_business_event,
    log_security_event,
    log_performance_metric,
    is_otel_available,
)

# Configuration and setup
from .config import ObservabilityConfig
from .setup import setup_observability

# Extractors - for advanced usage and custom extractors
from .extractors import (
    AttributeExtractor,
    HttpExtractor, 
    RpcExtractor,
    DatabaseExtractor,
    WorkflowExtractor,
    LangChainExtractor,
    CustomExtractor
)

# Specialized extractors
from .extractors.custom import BusinessOperationExtractor, MLOperationExtractor

__version__ = "2.0.0"

__all__ = [
    # Core API (recommended for most users)
    "trace",
    "trace_context",
    "get_current_span", 
    "add_span_event",
    "set_span_attribute",
    "metrics",
    "get_logger",
    
    # Setup and configuration
    "ObservabilityConfig",
    "setup_observability",
    "setup_logging",
    "configure_logging",
    "set_service_name",
    "set_global_service_name",
    "set_global_event_context",
    "get_global_event_context",
    "configure_event_schemas",
    "add_log_context",
    "clear_log_context",
    "get_log_context",
    
    # Convenience decorators
    "trace_http",
    "trace_rpc", 
    "trace_database",
    "trace_workflow",
    "trace_langchain",
    
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

    # Event logging (from psi_logging package)
    "log_operation_start",
    "log_operation_success", 
    "log_operation_error",
    "log_business_event",
    "log_security_event",
    "log_performance_metric",
] 