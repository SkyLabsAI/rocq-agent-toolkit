"""
Standalone Structured Logging Package

A universal Python logging package that provides structured JSON logging
with optional OpenTelemetry trace correlation. Works independently or
integrates seamlessly with observability packages.

Features:
- 🔗 Automatic trace correlation (when OpenTelemetry is available)
- 📊 Structured JSON output for Loki/ELK/etc.
- 🚀 Zero dependencies for basic usage
- 🔧 Framework-agnostic design
- 🎯 Business-friendly convenience methods

Quick Start:
    from observability.logging import get_logger, setup_logging

    # Setup once
    setup_logging(
        service_name="basic-logging-service",
        level="INFO",
        environment="dev"
    )

    # Use everywhere
    logger = get_logger(__name__)

    logger.info("User created successfully", 
            user_id="12345", 
            email="user@example.com",
            plan="premium")

    logger.error("Failed to process payment",
                user_id="12345",
                payment_amount=99.99,
                error_code="CARD_DECLINED")

Integration with Loki:
    All logs are structured JSON, perfect for Loki ingestion with
    automatic label extraction and search capabilities.

    Here is how to use it with Loki:
    
    from typing import List, Dict

    # Import our observability packages
    from observability import setup_observability, ObservabilityConfig, get_logger

    # Setup observability
    config = ObservabilityConfig(
        service_name="example-otel-loki-logging-v1",
        service_version="1.0.0",
        enable_logging=True
    )

    setup_observability(config)
    logger = get_logger(__name__)

    # Log with structured data
    logger.info("User logged in", 
                user_id="user123",
                email="john.doe@example.com",
                ip_address="192.168.1.100",
                user_agent="Mozilla/5.0...")

    # Log different levels
    logger.debug("Debug information", component="auth", action="validate_token")
    logger.warning("Rate limit approaching", user_id="user123", current_requests=45, limit=50)
    logger.error("Authentication failed", user_id="user123", reason="invalid_password", attempts=3)

    # Loki query examples
    {service_name="example-otel-loki-logging-v1"}
    {service_name="example-otel-loki-logging-v1"} |= "ERROR"
    {service_name="example-otel-loki-logging-v1"} | json | user_id="user123"
    
"""

from .core import (
    StructuredLogger,
    get_logger,
    setup_logging,
    set_global_service_name,
    set_global_event_context,
    get_global_event_context,
    configure_logging,
    configure_event_schemas,
    configure_auto_streaming,
    is_auto_streaming_enabled,
    get_accumulated_content_for_session,
    add_log_context,
    clear_log_context,
    get_log_context,
    is_otel_available,
)

from .events import (
    log_operation_start,
    log_operation_success, 
    log_operation_error,
    log_business_event,
    log_security_event,
    log_performance_metric,
    log_api_request,
    log_user_action,
)

from .context import (
    log_context,
    add_log_context,
    clear_log_context,
    get_log_context,
)

__version__ = "1.0.0"

__all__ = [
    # Core logging
    "StructuredLogger",
    "get_logger", 
    "setup_logging",
    "configure_logging",
    
    # Global configuration
    "set_global_service_name",
    "set_global_event_context",
    "get_global_event_context",
    
    # Event logging
    "log_operation_start",
    "log_operation_success",
    "log_operation_error", 
    "log_business_event",
    "log_security_event",
    "log_performance_metric",
    "log_api_request",
    "log_user_action",
    
    # Context management
    "log_context",
    "add_log_context",
    "clear_log_context", 
    "get_log_context",

    # Utilities
    "is_otel_available",
    "configure_event_schemas",
    "configure_auto_streaming",
    "is_auto_streaming_enabled",
    "get_accumulated_content_for_session",
] 