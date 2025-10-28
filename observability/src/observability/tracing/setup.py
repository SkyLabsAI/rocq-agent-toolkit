"""
Observability Setup for the Tracing Package

This module provides the main setup function to initialize the tracing and metrics
module with all the necessary components for OpenTelemetry instrumentation.
"""

import logging

from opentelemetry import metrics, propagate, trace
from opentelemetry.exporter.otlp.proto.grpc.metric_exporter import OTLPMetricExporter
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.instrumentation.grpc import (
    GrpcInstrumentorClient,
    GrpcInstrumentorServer,
)
from opentelemetry.instrumentation.logging import LoggingInstrumentor
from opentelemetry.instrumentation.requests import RequestsInstrumentor
from opentelemetry.instrumentation.urllib3 import URLLib3Instrumentor
from opentelemetry.sdk.metrics import MeterProvider
from opentelemetry.sdk.metrics.export import PeriodicExportingMetricReader
from opentelemetry.sdk.resources import Resource
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.trace.propagation.tracecontext import TraceContextTextMapPropagator

from ..logging.setup import setup_logging
from .config import ObservabilityConfig

logger = logging.getLogger(__name__)

_initialized = False


def setup_observability(config: ObservabilityConfig) -> None:
    """
    Setup OpenTelemetry logging, tracing, and metrics with the provided configuration.

    Args:
        config: ObservabilityConfig instance with desired settings
    """
    global _initialized
    if _initialized:
        logger.warning("Observability already initialized, skipping setup")
        return

    # 1. Setup logging first, if enabled
    if config.enable_logging:
        setup_logging(config)

    # 2. Setup tracing
    logger.debug(f"Setting up tracing for service: {config.service_name}")

    resource_attributes = {
        "service.name": config.service_name,
        "service.version": config.service_version,
        "service.namespace": config.service_namespace,
    }
    if config.environment:
        resource_attributes["deployment.environment"] = config.environment
    resource = Resource.create(resource_attributes)

    if config.enable_tracing:
        _setup_tracing(config, resource)

    if config.enable_metrics:
        _setup_metrics(config, resource)

    _setup_auto_instrumentation(config)

    _initialized = True
    logger.debug("Observability setup completed successfully")


def _setup_tracing(config: ObservabilityConfig, resource: Resource) -> None:
    """Setup distributed tracing."""
    logger.debug("Setting up tracing...")

    trace.set_tracer_provider(TracerProvider(resource=resource))

    otlp_exporter = OTLPSpanExporter(
        endpoint=config.otlp_endpoint,
        insecure=config.otlp_insecure,
        headers=config.custom_headers,
    )

    span_processor = BatchSpanProcessor(
        otlp_exporter,
        export_timeout_millis=config.batch_export_timeout_ms,
        max_export_batch_size=config.max_export_batch_size,
    )
    trace.get_tracer_provider().add_span_processor(span_processor)

    propagate.set_global_textmap(TraceContextTextMapPropagator())

    logger.debug("Tracing setup completed")


def _setup_metrics(config: ObservabilityConfig, resource: Resource) -> None:
    """Setup metrics collection."""
    logger.debug("Setting up metrics...")

    metric_exporter = OTLPMetricExporter(
        endpoint=config.otlp_endpoint,
        insecure=config.otlp_insecure,
        headers=config.custom_headers,
    )

    metric_reader = PeriodicExportingMetricReader(
        exporter=metric_exporter,
        export_interval_millis=config.metric_export_interval_ms,
        export_timeout_millis=config.batch_export_timeout_ms,
    )

    metrics.set_meter_provider(
        MeterProvider(resource=resource, metric_readers=[metric_reader])
    )

    logger.debug("Metrics setup completed")


def _setup_auto_instrumentation(config: ObservabilityConfig) -> None:
    """Setup automatic instrumentation for common libraries."""
    logger.debug("Setting up automatic instrumentation...")

    try:
        GrpcInstrumentorServer().instrument()
        GrpcInstrumentorClient().instrument()
        logger.debug("gRPC instrumentation enabled")
    except Exception as e:
        logger.warning(f"Failed to instrument gRPC: {e}")

    try:
        LoggingInstrumentor().instrument(set_logging_format=False)
        logger.debug("Logging instrumentation enabled")
    except Exception as e:
        logger.warning(f"Failed to instrument logging: {e}")

    try:
        RequestsInstrumentor().instrument()
        URLLib3Instrumentor().instrument()
        logger.debug("HTTP libraries instrumentation enabled")
    except Exception as e:
        logger.warning(f"Failed to instrument HTTP libraries: {e}")

    if config.enable_langsmith:
        _setup_langsmith_instrumentation(config)

    logger.debug("Automatic instrumentation setup completed")


def _setup_langsmith_instrumentation(config: ObservabilityConfig) -> None:
    """Setup LangSmith instrumentation for LangChain/LangGraph operations."""
    logger.debug("Setting up LangSmith instrumentation...")

    try:
        import os

        if config.enable_langsmith:
            os.environ["LANGSMITH_OTEL_ENABLED"] = "true"
            os.environ["OTEL_EXPORTER_OTLP_ENDPOINT"] = config.otlp_endpoint
            os.environ["LANGSMITH_TRACING"] = "true"

            if config.langsmith_service_suffix:
                langsmith_service_name = (
                    f"{config.service_name}-{config.langsmith_service_suffix}"
                )
                os.environ["LANGSMITH_OTEL_SERVICE_NAME"] = langsmith_service_name
            else:
                os.environ["LANGSMITH_OTEL_SERVICE_NAME"] = config.service_name

            os.environ["LANGSMITH_OTEL_ENDPOINT"] = config.otlp_endpoint

            if config.langchain_tracing_v2:
                os.environ["LANGCHAIN_TRACING_V2"] = "true"

            logger.debug("LangSmith instrumentation configured")
        else:
            os.environ["LANGSMITH_TRACING"] = "false"
            logger.debug("LangSmith instrumentation disabled")

    except ImportError:
        logger.warning(
            "LangSmith libraries not available, skipping LangSmith instrumentation"
        )
    except Exception as e:
        logger.warning(f"Failed to setup LangSmith instrumentation: {e}")
