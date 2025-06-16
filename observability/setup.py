"""
Observability Setup

This module provides the main setup function to initialize OpenTelemetry
instrumentation with all the necessary components.
"""

import logging
from typing import Optional

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
    
    logger.info(f"Setting up observability for service: {config.service_name}")
    
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
    
    # Setup automatic instrumentation
    _setup_auto_instrumentation(config)
    
    _initialized = True
    _current_config = config
    
    logger.info("OpenTelemetry observability setup completed successfully")
    logger.info(f"Service: {config.service_name}")
    logger.info(f"OTLP Endpoint: {config.otlp_endpoint}")
    logger.info(f"Features - Tracing: {config.enable_tracing}, Metrics: {config.enable_metrics}, Logging: {config.enable_logging}")


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
    from psi_logging import setup_logging
    setup_logging(
        service_name=config.service_name,
        level=config.log_level,
        format_json=config.log_format_json,
        environment=config.environment
    )
    
    # 2. Setup OTLP log export for shipping to Loki/collectors
    _setup_otlp_log_export(config)
    
    logger.debug("Structured logging setup completed")


def _setup_otlp_log_export(config: ObservabilityConfig) -> None:
    """Setup OTLP log export to send structured logs to collectors."""
    logger.debug("Setting up OTLP log export...")
    
    # Create resource with service information
    resource = Resource.create(config.effective_resource_attributes)
    
    # Set up logger provider
    logger_provider = LoggerProvider(resource=resource)
    _logs.set_logger_provider(logger_provider)
    
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
    
    # Create OTLP logging handler and add to root logger
    otlp_handler = LoggingHandler(
        level=getattr(logging, config.log_level.upper()),
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
    
    # Instrument logging
    try:
        LoggingInstrumentor().instrument(set_logging_format=True)
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