"""
Observability Setup for the Logging Package

This module provides the main setup function to initialize the logging module
with all the necessary components for structured logging, OTLP export, and
asynchronous processing.
"""

import logging
from typing import List, Dict

from opentelemetry import _logs
from opentelemetry.exporter.otlp.proto.grpc._log_exporter import OTLPLogExporter
from opentelemetry.sdk._logs import LoggerProvider, LoggingHandler
from opentelemetry.sdk._logs.export import BatchLogRecordProcessor
from opentelemetry.sdk.resources import Resource

from .config import LoggingConfig
from .core import setup_logging as core_setup_logging, configure_event_schemas

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
        environment=config.environment
    )
    
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
        headers=config.custom_headers
    )
    
    logger_provider.add_log_record_processor(
        BatchLogRecordProcessor(log_exporter)
    )
    
    otlp_handler = FixedLoggingHandler(logger_provider=logger_provider)
    
    root_logger = logging.getLogger()
    root_logger.addHandler(otlp_handler)
    
    logger.debug("OTLP log export setup completed")
