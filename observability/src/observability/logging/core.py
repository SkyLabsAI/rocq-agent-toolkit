"""
Core structured logging functionality.

This module provides the main logging infrastructure with optional
OpenTelemetry integration for trace correlation.
"""

import inspect
import json
import logging
import os
import socket
import time
from contextvars import ContextVar  # Async-safe per-task storage
from typing import Any, Dict, List, Optional

# Optional OpenTelemetry integration
try:
    from opentelemetry import trace as otel_trace

    OTEL_AVAILABLE = True
except ImportError:
    OTEL_AVAILABLE = False


class StructuredLogger:
    """
    Structured logger with automatic trace correlation.

    This logger automatically includes trace information in log entries
    and formats them as structured JSON for better observability.
    Works with or without OpenTelemetry.
    """

    def __init__(
        self,
        name: str,
        service_name: Optional[str] = None,
        event_context: Optional[str] = None,
    ):
        """
        Initialize structured logger.

        Args:
            name: Logger name (usually module name)
            service_name: Service name to include in logs
            event_context: Default event type to apply to all log entries
        """
        self.logger = logging.getLogger(name)
        self.service_name = service_name
        self.name = name
        self.event_context = event_context

    def debug(self, message: str, *args: Any, **kwargs: Any):
        """Log debug message with structured data."""
        self._log(logging.DEBUG, message, *args, **kwargs)

    def info(self, message: str, *args: Any, **kwargs: Any):
        """Log info message with structured data."""
        self._log(logging.INFO, message, *args, **kwargs)

    def warning(self, message: str, *args: Any, **kwargs: Any):
        """Log warning message with structured data."""
        self._log(logging.WARNING, message, *args, **kwargs)

    def error(self, message: str, *args: Any, **kwargs: Any):
        """Log error message with structured data."""
        self._log(logging.ERROR, message, *args, **kwargs)

    def critical(self, message: str, *args: Any, **kwargs: Any):
        """Log critical message with structured data."""
        self._log(logging.CRITICAL, message, *args, **kwargs)

    def exception(self, message: str, *args: Any, **kwargs: Any):
        """Log exception with structured data and stack trace."""
        kwargs["exc_info"] = True
        self._log(logging.ERROR, message, *args, **kwargs)

    def _log(self, level: int, message: str, *args: Any, **kwargs: Any):
        """Internal logging method that adds structure and trace correlation."""
        if not self.logger.isEnabledFor(level):
            return

        # Format message with args if provided (standard Python logging behavior)
        if args:
            try:
                formatted_message = message % args
            except (TypeError, ValueError):
                # If formatting fails, just use the original message and log the error
                formatted_message = message
                kwargs[
                    "_format_error"
                ] = f"Failed to format message '{message}' with args {args}"
        else:
            formatted_message = message

        # Apply event context if configured
        if self.event_context:
            kwargs = self._apply_event_context(self.event_context, kwargs)

        # Get caller information for both JSON and console logs
        caller_info = self._get_caller_info()

        # Build structured log entry
        log_entry = {
            "timestamp": time.time(),
            "level": logging.getLevelName(level),
            "message": formatted_message,
            "logger": self.name,
        }

        # Add caller information to JSON logs
        if caller_info:
            log_entry.update(caller_info)

        # Add service name if available
        if self.service_name:
            log_entry["service"] = self.service_name

        # Add trace correlation if OpenTelemetry is available
        if OTEL_AVAILABLE:
            self._add_trace_correlation(log_entry)

        # Add any global context
        global_context = get_log_context()
        if global_context:
            log_entry.update(global_context)

        # Add custom fields
        for key, value in kwargs.items():
            if key != "exc_info":  # Skip special logging parameters
                # Flatten nested objects for better readability
                if isinstance(value, dict):
                    for nested_key_str, nested_value in value.items():  # type: ignore
                        log_entry[f"{key}.{nested_key_str}"] = nested_value
                else:
                    log_entry[key] = value

        # Log the structured entry
        try:
            # Pass caller info to handler via extra to avoid double stack walk
            extra_data = {}
            if caller_info:
                extra_data["_caller_info"] = caller_info

            if kwargs.get("exc_info"):
                self.logger.log(
                    level, json.dumps(log_entry), exc_info=True, extra=extra_data
                )
            else:
                self.logger.log(level, json.dumps(log_entry), extra=extra_data)
        except json.JSONDecodeError as e:
            self.logger.error(f"Failed to log message: {e}")
            self.logger.info(f"Log entry as message string: \n{log_entry}")
        except Exception as e:
            self.logger.error(f"Failed to log message: {e}")

    def _apply_event_context(
        self, event_type: str, kwargs: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Apply event context and schema filtering to log kwargs."""
        # Filter payload using schema if one is configured
        allowed_fields = _event_schemas.get(event_type)
        if allowed_fields is not None:
            kwargs = {
                k: v
                for k, v in kwargs.items()
                if k in allowed_fields or k == "exc_info"
            }

        # Add event_type to the log entry
        kwargs["event_type"] = event_type

        return kwargs

    def _add_trace_correlation(self, log_entry: Dict[str, Any]):
        """Add OpenTelemetry trace correlation if available."""
        try:
            span = otel_trace.get_current_span()
            if span and span.is_recording():
                span_context = span.get_span_context()
                if span_context.is_valid:
                    log_entry["trace_id"] = format(span_context.trace_id, "032x")
                    log_entry["span_id"] = format(span_context.span_id, "016x")
        except Exception:
            # Silently ignore trace correlation errors
            pass

    def _get_caller_info(self) -> Dict[str, Any]:
        """Get caller information by inspecting the call stack."""
        stack = inspect.stack()

        caller_frame = None
        # Find the first frame that's not part of the logging infrastructure
        for frame_info in stack:
            frame_filename = frame_info.filename
            frame_function = frame_info.function

            # Skip frames from logging infrastructure
            if (
                "logging" in frame_filename
                or "logging" in frame_filename
                or "opentelemetry" in frame_filename
                or
                # Also skip our own logger methods
                frame_function
                in [
                    "_log",
                    "log",
                    "emit",
                    "handle",
                    "callHandlers",
                    "debug",
                    "info",
                    "warning",
                    "error",
                    "critical",
                    "exception",
                ]
            ):
                continue

            # This is likely the actual caller
            caller_frame = frame_info
            break

        # Return caller information as dict
        if caller_frame:
            return {
                "file": os.path.basename(caller_frame.filename),
                "line": caller_frame.lineno,
                "function": caller_frame.function,
            }

        return {}

    # ------------------------------------------------------------------
    # Event-based structured logging
    # ------------------------------------------------------------------
    def set_event_context(self, event_type: Optional[str]):
        """Set or clear the event context for this logger instance.

        Args:
            event_type: Event type to use for all log entries, or None to clear
        """
        self.event_context = event_type


# Global state
_loggers: Dict[str, StructuredLogger] = {}
_global_service_name: Optional[str] = None

# ---------------------------------------------------------------------------
# Async-safe, per-task log context
# ---------------------------------------------------------------------------
# A single mutable dict (`_log_context`) is unsafe when multiple threads or
# asyncio tasks mutate it concurrently.  We replace it with a ContextVar that
# delivers an *independent* copy for every logical execution context.
# ---------------------------------------------------------------------------

_log_context_var: ContextVar[Dict[str, Any]] = ContextVar(
    "_log_context_var", default={}
)

# Per-event schemas. The value is a list of allowed payload keys.
_event_schemas: Dict[str, List[str]] = {}

# Global event context configuration
_global_event_context: Optional[str] = None


def get_logger(
    name: str, service_name: Optional[str] = None, event_context: Optional[str] = None
) -> StructuredLogger:
    """
    Get a structured logger instance.

    Args:
        name: Logger name (usually __name__)
        service_name: Service name (uses global if not provided)
        event_context: Event context for this logger (uses global if not provided)

    Returns:
        StructuredLogger instance

    Examples:
        # Basic usage
        logger = get_logger(__name__)
        logger.info("User created", user_id="123", email="user@example.com")

        # With event context
        logger = get_logger(__name__, event_context="langgraph")
        logger.info("Node executed", node_name="process_input", status="success")
        # This will automatically include event_type="langgraph" and apply schema
        # filtering
    """
    effective_service_name = service_name or _global_service_name
    effective_event_context = event_context or _global_event_context
    cache_key = f"{name}:{effective_service_name}:{effective_event_context}"

    if cache_key not in _loggers:
        _loggers[cache_key] = StructuredLogger(
            name, effective_service_name, effective_event_context
        )

    return _loggers[cache_key]


def setup_logging(
    service_name: str,
    level: str = "INFO",
    format_json: bool = True,
    loki_endpoint: Optional[str] = None,
    environment: Optional[str] = None,
):
    """
    Complete logging setup for a service.

    Args:
        service_name: Name of the service
        level: Logging level
        format_json: Whether to use JSON formatting
        loki_endpoint: Optional Loki endpoint for direct shipping
        environment: Environment name (dev, staging, prod)

    Example:
        setup_logging(
            service_name="user-service",
            level="INFO",
            environment="production"
        )
    """
    set_global_service_name(service_name)
    configure_logging(level, format_json)

    # Add environment to global context
    if environment:
        add_log_context("environment", environment)

    # Add hostname/container info
    hostname = _get_hostname()
    add_log_context("hostname", hostname)

    logger = get_logger("observability.logging.setup")
    logger.debug(
        "Logging system initialized",
        service=service_name,
        log_level=level,
        json_format=format_json,
        otel_available=OTEL_AVAILABLE,
    )


def set_global_service_name(service_name: str):
    """
    Set the global service name for all loggers.

    Args:
        service_name: Service name to use globally
    """
    global _global_service_name
    _global_service_name = service_name


def set_global_event_context(event_context: Optional[str]):
    """
    Set the global event context for all new loggers.

    Args:
        event_context: Event type to use globally, or None to clear
    """
    global _global_event_context
    _global_event_context = event_context


def get_global_event_context() -> Optional[str]:
    """
    Get the current global event context.

    Returns:
        Current global event context, or None if not set
    """
    return _global_event_context


def configure_logging(level: str = "INFO", format_json: bool = True):
    """
    Configure the Python logging system.

    Args:
        level: Logging level ("DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL")
        format_json: Whether to format logs as JSON
    """
    log_level = getattr(logging, level.upper(), logging.INFO)

    # Configure root logger
    logging.basicConfig(
        level=log_level,
        format=(
            "%(message)s"
            if format_json
            else "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
        ),
        datefmt="%Y-%m-%d %H:%M:%S",
        force=True,  # Ensure reconfiguration even if handlers exist
    )

    # Disable some noisy loggers
    logging.getLogger("urllib3").setLevel(logging.WARNING)
    logging.getLogger("requests").setLevel(logging.WARNING)
    logging.getLogger("opentelemetry").setLevel(logging.WARNING)


def add_log_context(key: str, value: Any) -> None:
    """Add / override a field in the *task-local* log context.

    Uses a snapshot copy to avoid mutating the dict another task may be using.
    Safe for threads and asyncio tasks.
    """
    ctx = _log_context_var.get().copy()
    ctx[key] = value
    _log_context_var.set(ctx)


def clear_log_context() -> None:
    """Remove every field from the *current task’s* context."""
    _log_context_var.set({})


def get_log_context() -> Dict[str, Any]:
    """Return a *copy* of the current task-local log context."""
    return _log_context_var.get().copy()


def is_otel_available() -> bool:
    """Check if OpenTelemetry is available for trace correlation."""
    return OTEL_AVAILABLE


def _get_hostname() -> str:
    """
    Get hostname using the most reliable cross-platform method.

    Returns:
        str: The system hostname, or 'unknown' if unable to determine
    """
    try:
        # Try socket.gethostname() first - most reliable cross-platform method
        hostname = socket.gethostname()
        if hostname:
            return hostname
    except Exception:
        pass

    try:
        # Fallback to environment variables
        hostname = os.getenv("HOSTNAME") or os.getenv("COMPUTERNAME")
        if hostname:
            return hostname
    except Exception:
        pass

    # Final fallback
    return "unknown"


def configure_event_schemas(schema_dict: Dict[str, List[str]]) -> None:
    """Configure the per-event payload schemas.

    The *schema_dict* should map *event_type* strings to a list of allowed
    payload keys. Call this once at application start-up (see
    ``observability.setup._setup_logging_module``).
    """
    global _event_schemas
    _event_schemas = schema_dict.copy()
