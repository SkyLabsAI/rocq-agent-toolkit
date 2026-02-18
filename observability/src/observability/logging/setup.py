"""
Observability Setup for the Logging Package

This module provides the main setup function to initialize the logging module
with all the necessary components for structured logging, OTLP export, and
asynchronous processing.
"""

import logging
import sys

from opentelemetry import _logs
from opentelemetry.exporter.otlp.proto.grpc._log_exporter import OTLPLogExporter
from opentelemetry.sdk._logs import LoggerProvider, LoggingHandler
from opentelemetry.sdk._logs.export import BatchLogRecordProcessor
from opentelemetry.sdk.resources import Resource

from .config import LoggingConfig
from .core import configure_event_schemas
from .core import setup_logging as core_setup_logging

logger = logging.getLogger(__name__)


def setup_logging(config: LoggingConfig) -> None:
    """
    Setup structured logging with OTLP export.

    Args:
        config: Configuration for the logging module.
    """
    logger.debug("Setting up structured logging...")

    # 1. Setup structured logging for console output and formatting
    core_setup_logging(
        service_name=config.service_name,
        level=config.log_level,
        format_json=config.log_format_json,
        environment=config.environment,
    )

    # 1a. Optionally disable console/terminal logging while keeping other handlers
    # From all the stream handlers, keep only the ones that are not stdout or stderr
    if not config.enable_console_logging:
        root_logger = logging.getLogger()

        def is_console_stream_handler(h: logging.Handler) -> bool:
            return isinstance(h, logging.StreamHandler) and getattr(
                h, "stream", None
            ) in {sys.stdout, sys.stderr}

        root_logger.handlers = [
            h for h in root_logger.handlers if not is_console_stream_handler(h)
        ]
        logger.debug("Console (stdout/stderr) logging disabled by configuration")

    # 1b. Populate event schemas so loggers can filter payloads appropriately
    event_configs = {
        "training": config.training_event_config,
        "workflow": config.workflow_event_config,
        "evaluation": config.evaluation_event_config,
        "langgraph": config.langgraph_event_config,
    }
    schema_dict = {
        name: event_config.allowed_fields()
        for name, event_config in event_configs.items()
        if event_config and event_config.enabled
    }

    if schema_dict:
        configure_event_schemas(schema_dict)

    # 2. Setup OTLP log export for shipping to Loki/collectors (only if enabled)
    if config.enable_otlp_log_export:
        _setup_otlp_log_export(config)
    else:
        logger.debug("OTLP log export disabled by configuration")

    logger.debug("Structured logging setup completed")


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
        # Check if caller info was already provided by StructuredLogger
        if hasattr(record, "_caller_info") and record._caller_info:
            # Use the pre-computed caller info to avoid double stack walk
            caller_info = record._caller_info
            # Convert the dict format to LogRecord fields
            if "file" in caller_info:
                record.filename = caller_info["file"]
                record.pathname = caller_info[
                    "file"
                ]  # Will be overridden below if we have full path
            if "function" in caller_info:
                record.funcName = caller_info["function"]
            if "line" in caller_info:
                record.lineno = caller_info["line"]
            if "file" in caller_info:
                record.module = caller_info["file"].replace(".py", "")

        # Call the parent emit method
        super().emit(record)


def _setup_otlp_log_export(config: LoggingConfig) -> None:
    """Setup OTLP log export to send structured logs to collectors."""
    logger.debug("Setting up OTLP log export...")

    resource_attributes = {
        "service.name": config.service_name,
        "service.version": config.service_version,
        "service.namespace": config.service_namespace,
    }
    if config.environment:
        resource_attributes["deployment.environment"] = config.environment

    resource = Resource.create(resource_attributes)

    logger_provider = LoggerProvider(resource=resource)
    _logs.set_logger_provider(logger_provider)

    log_exporter = OTLPLogExporter(
        endpoint=config.otlp_endpoint,
        insecure=config.otlp_insecure,
        headers=config.custom_headers,
    )

    logger_provider.add_log_record_processor(BatchLogRecordProcessor(log_exporter))

    otlp_handler = FixedLoggingHandler(logger_provider=logger_provider)

    root_logger = logging.getLogger()
    root_logger.addHandler(otlp_handler)

    logger.debug("OTLP log export setup completed")
