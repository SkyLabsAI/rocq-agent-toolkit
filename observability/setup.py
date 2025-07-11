"""
Observability Setup

This module provides the main setup function to initialize OpenTelemetry
instrumentation with all the necessary components.
"""

import logging
import uuid
from typing import Optional, Dict, List, Any

from opentelemetry import trace, metrics, _logs
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.exporter.otlp.proto.grpc.metric_exporter import OTLPMetricExporter
from opentelemetry.exporter.otlp.proto.grpc._log_exporter import OTLPLogExporter
from opentelemetry.instrumentation.grpc import GrpcInstrumentorServer, GrpcInstrumentorClient
from opentelemetry.instrumentation.logging import LoggingInstrumentor
from opentelemetry.instrumentation.requests import RequestsInstrumentor
from opentelemetry.instrumentation.urllib3 import URLLib3Instrumentor
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.sdk.metrics import MeterProvider
from opentelemetry.sdk.metrics.export import PeriodicExportingMetricReader
from opentelemetry.sdk.resources import Resource
from opentelemetry.sdk._logs import LoggerProvider, LoggingHandler
from opentelemetry.sdk._logs.export import BatchLogRecordProcessor
from opentelemetry._logs import set_logger_provider as _set_logger_provider
from opentelemetry.util.types import AttributeValue
from opentelemetry.sdk.trace.sampling import TraceIdRatioBased

from .config import ObservabilityConfig

logger = logging.getLogger(__name__)

# Global state to track initialization
_initialized = False
_current_config: Optional[ObservabilityConfig] = None


def setup_observability(config: ObservabilityConfig) -> None:
    """
    Setup OpenTelemetry observability with the provided configuration.
    
    This function should be called once at application startup, before any
    other observability instrumentation or gRPC operations.
    
    Args:
        config: ObservabilityConfig instance with desired settings
        
    Raises:
        RuntimeError: If observability has already been initialized
    """
    global _initialized, _current_config
    
    if _initialized:
        if _current_config and _current_config.service_name != config.service_name:
            raise RuntimeError(
                f"Observability already initialized for service '{_current_config.service_name}'. "
                f"Cannot reinitialize for service '{config.service_name}'"
            )
        logger.warning("Observability already initialized, skipping setup")
        return
    
    logger.debug(f"Setting up observability for service: {config.service_name}")
    
    # Create resource with service information
    resource = Resource.create(config.effective_resource_attributes)
    
    # Setup tracing if enabled
    if config.enable_tracing:
        _setup_tracing(config, resource)
    
    # Setup metrics if enabled  
    if config.enable_metrics:
        _setup_metrics(config, resource)
    
    # Setup logging if enabled (using psi_logging package)
    if config.enable_logging:
        _setup_psi_logging(config)
    
        # Add a unique run_id to all logs for this session
        from psi_verifier.psi_logging import add_log_context
        run_id = str(uuid.uuid4())
        add_log_context("run_id", run_id)
        logger.debug(f"Added unique run_id to log context: {run_id}")
        
        # Add user_id and session_id to log context if provided
        if config.user_id:
            add_log_context("user_id", config.user_id)
            logger.debug(f"Added user_id to log context: {config.user_id}")
        
        if config.session_id:
            add_log_context("session_id", config.session_id)
            logger.debug(f"Added session_id to log context: {config.session_id}")
    # Setup automatic instrumentation
    _setup_auto_instrumentation(config)
    
    _initialized = True
    _current_config = config
    
    logger.debug("OpenTelemetry observability setup completed successfully")
    logger.debug(f"Service: {config.service_name}")
    logger.debug(f"OTLP Endpoint: {config.otlp_endpoint}")
    logger.debug(f"Features - Tracing: {config.enable_tracing}, Metrics: {config.enable_metrics}, Logging: {config.enable_logging}")


def _setup_tracing(config: ObservabilityConfig, resource: Resource) -> None:
    """Setup distributed tracing."""
    logger.debug("Setting up tracing...")
    
    # Set up tracer provider
    trace.set_tracer_provider(TracerProvider(resource=resource))
    
    # Configure OTLP exporter for traces
    otlp_exporter = OTLPSpanExporter(
        endpoint=config.otlp_endpoint,
        insecure=config.otlp_insecure,
        headers=config.custom_headers
    )
    
    # Add span processor with batch configuration
    span_processor = BatchSpanProcessor(
        otlp_exporter,
        export_timeout_millis=config.batch_export_timeout_ms,
        max_export_batch_size=config.max_export_batch_size
    )
    trace.get_tracer_provider().add_span_processor(span_processor)
    
    logger.debug("Tracing setup completed")


def _setup_metrics(config: ObservabilityConfig, resource: Resource) -> None:
    """Setup metrics collection."""
    logger.debug("Setting up metrics...")
    
    # Configure OTLP metric exporter
    metric_exporter = OTLPMetricExporter(
        endpoint=config.otlp_endpoint,
        insecure=config.otlp_insecure,
        headers=config.custom_headers
    )
    
    # Create metric reader with periodic export
    metric_reader = PeriodicExportingMetricReader(
        exporter=metric_exporter,
        export_interval_millis=config.metric_export_interval_ms,
        export_timeout_millis=config.batch_export_timeout_ms
    )
    
    # Set up meter provider
    metrics.set_meter_provider(MeterProvider(
        resource=resource,
        metric_readers=[metric_reader]
    ))
    
    logger.debug("Metrics setup completed")


def _setup_psi_logging(config: ObservabilityConfig) -> None:
    """Setup structured logging with OTLP export."""
    logger.debug("Setting up structured logging...")
    
    # 1. Setup structured logging for console output and formatting
    from psi_verifier.psi_logging import setup_logging
    from psi_verifier.psi_logging.core import configure_event_schemas  # local import to avoid circular deps
    setup_logging(
        service_name=config.service_name,
        level=config.log_level,
        format_json=config.log_format_json,
        environment=config.environment
    )
    
    # 1b. Populate event schemas so loggers can filter payloads appropriately
    schema_dict: Dict[str, List[str]] = {}
    if config.training_event_config and config.training_event_config.enabled:
        schema_dict["training"] = config.training_event_config.allowed_fields()
    if config.workflow_event_config and config.workflow_event_config.enabled:
        schema_dict["workflow"] = config.workflow_event_config.allowed_fields()
    if config.evaluation_event_config and config.evaluation_event_config.enabled:
        schema_dict["evaluation"] = config.evaluation_event_config.allowed_fields()
    if config.langgraph_event_config and config.langgraph_event_config.enabled:
        schema_dict["langgraph"] = config.langgraph_event_config.allowed_fields()

    if schema_dict:
        configure_event_schemas(schema_dict)
    
    # 1c. Configure contextual logging if a specific event context is preferred
    # This allows users to set a default event context for all new loggers
    _setup_contextual_logging(config)
    
    # 2. Setup OTLP log export for shipping to Loki/collectors
    _setup_otlp_log_export(config)
    
    logger.debug("Structured logging setup completed")


def _setup_contextual_logging(config: ObservabilityConfig) -> None:
    """Setup contextual logging based on configuration."""
    from psi_verifier.psi_logging import set_global_event_context
    
    # Check if any event config is enabled and should be used as default context
    # Priority: langgraph -> training -> workflow -> evaluation
    default_context = None
    
    if config.langgraph_event_config and config.langgraph_event_config.enabled:
        default_context = "langgraph"
    elif config.training_event_config and config.training_event_config.enabled:
        default_context = "training"
    elif config.workflow_event_config and config.workflow_event_config.enabled:
        default_context = "workflow"
    elif config.evaluation_event_config and config.evaluation_event_config.enabled:
        default_context = "evaluation"
    
    if default_context:
        set_global_event_context(default_context)
        logger.debug(f"Set global event context to: {default_context}")
    

class FixedLoggingHandler(LoggingHandler):
    """
    Custom LoggingHandler that captures correct caller information.
    
    This handler fixes the issue where code_file_path, code_function_name,
    and code_line_number point to logger internals instead of the actual caller.
    """
    
    def emit(self, record: logging.LogRecord) -> None:
        """
        Emit a log record with correct caller information.
        
        Args:
            record: The log record to emit
        """
        # Fix the caller information by looking deeper in the stack
        # Skip frames related to logging infrastructure
        import inspect
        
        # Get the current stack
        stack = inspect.stack()
        
        # Find the first frame that's not part of the logging infrastructure
        caller_frame = None
        for frame_info in stack:
            frame_filename = frame_info.filename
            frame_function = frame_info.function
            
            # Skip frames from logging infrastructure
            if (
                'logging' in frame_filename or
                'psi_logging' in frame_filename or
                'opentelemetry' in frame_filename or
                frame_function in ['_log', 'log', 'emit', 'handle', 'callHandlers']
            ):
                continue
            
            # This is likely the actual caller
            caller_frame = frame_info
            break
        
        # Update the record with correct caller information
        if caller_frame:
            record.pathname = caller_frame.filename
            record.filename = caller_frame.filename.split('/')[-1]
            record.funcName = caller_frame.function
            record.lineno = caller_frame.lineno
            record.module = caller_frame.filename.split('/')[-1].replace('.py', '')
        
        # Call the parent emit method
        super().emit(record)


def _setup_otlp_log_export(config: ObservabilityConfig) -> None:
    """Setup OTLP log export to send structured logs to collectors."""
    logger.debug("Setting up OTLP log export...")
    
    # Create resource with service information
    resource = Resource.create(config.effective_resource_attributes)
    
    # Set up logger provider
    logger_provider = LoggerProvider(resource=resource)
    _set_logger_provider(logger_provider)
    
    # Configure OTLP Log Exporter
    log_exporter = OTLPLogExporter(
        endpoint=config.otlp_endpoint,
        insecure=config.otlp_insecure,
        headers=config.custom_headers
    )
    
    # Add batch log processor
    logger_provider.add_log_record_processor(
        BatchLogRecordProcessor(
            log_exporter,
            export_timeout_millis=config.batch_export_timeout_ms,
            max_export_batch_size=config.max_export_batch_size
        )
    )
    
    # Create custom OTLP logging handler with fixed caller information
    otlp_handler = FixedLoggingHandler(
        # level=getattr(logging, config.log_level.upper()),
        logger_provider=logger_provider
    )
    
    # Add OTLP handler to root logger (in addition to console handler)
    root_logger = logging.getLogger()
    root_logger.addHandler(otlp_handler)
    
    logger.debug("OTLP log export setup completed")


def _setup_auto_instrumentation(config: ObservabilityConfig) -> None:
    """Setup automatic instrumentation for common libraries."""
    logger.debug("Setting up automatic instrumentation...")
    
    # Instrument gRPC (both server and client)
    try:
        GrpcInstrumentorServer().instrument()
        GrpcInstrumentorClient().instrument()
        logger.debug("gRPC instrumentation enabled")
    except Exception as e:
        logger.warning(f"Failed to instrument gRPC: {e}")
    
    # Instrument logging without format override to avoid duplicate fields
    try:
        LoggingInstrumentor().instrument(set_logging_format=False)
        logger.debug("Logging instrumentation enabled") 
    except Exception as e:
        logger.warning(f"Failed to instrument logging: {e}")
    
    # Instrument HTTP libraries
    try:
        RequestsInstrumentor().instrument()
        URLLib3Instrumentor().instrument()
        logger.debug("HTTP libraries instrumentation enabled")
    except Exception as e:
        logger.warning(f"Failed to instrument HTTP libraries: {e}")
    
    # Instrument LangSmith/LangChain if enabled
    if config.enable_langsmith:
        _setup_langsmith_instrumentation(config)
    
    logger.debug("Automatic instrumentation setup completed")


def _setup_langsmith_instrumentation(config: ObservabilityConfig) -> None:
    """Setup LangSmith instrumentation for LangChain/LangGraph operations."""
    logger.debug("Setting up LangSmith instrumentation...")
    
    try:
        import os
        
        # Set LangSmith environment variables for OpenTelemetry integration
        os.environ["LANGSMITH_OTEL_ENABLED"] = "true"
        
        # Use a dedicated service name for LangSmith traces if suffix is configured
        if config.langsmith_service_suffix:
            langsmith_service_name = f"{config.service_name}-{config.langsmith_service_suffix}"
            os.environ["LANGSMITH_OTEL_SERVICE_NAME"] = langsmith_service_name
        else:
            os.environ["LANGSMITH_OTEL_SERVICE_NAME"] = config.service_name
        
        # Set OTLP endpoint for LangSmith
        os.environ["LANGSMITH_OTEL_ENDPOINT"] = config.otlp_endpoint
        
        logger.debug(f"LangSmith instrumentation configured")
        logger.debug(f"LangSmith service name: {os.environ.get('LANGSMITH_OTEL_SERVICE_NAME')}")
        
    except ImportError:
        logger.warning("LangSmith libraries not available, skipping LangSmith instrumentation")
    except Exception as e:
        logger.warning(f"Failed to setup LangSmith instrumentation: {e}")


def is_observability_enabled() -> bool:
    """Check if observability has been initialized."""
    return _initialized


def get_current_config() -> Optional[ObservabilityConfig]:
    """Get the current observability configuration."""
    return _current_config


def reset_observability() -> None:
    """
    Reset observability state. 
    
    WARNING: This should only be used in testing scenarios.
    In production, observability should be initialized once at startup.
    """
    global _initialized, _current_config
    _initialized = False
    _current_config = None
    logger.warning("Observability state has been reset") 