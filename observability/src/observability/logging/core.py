"""
Core structured logging functionality.

This module provides the main logging infrastructure with optional
OpenTelemetry integration for trace correlation.
"""

import json
import logging
import time
import uuid
import threading
from typing import Any, Dict, Optional, List, Union
from dataclasses import dataclass, field
import os
from contextvars import ContextVar  # Async-safe per-task storage
from contextvars import ContextVar  # Async-safe per-task storage
import socket
import inspect
# Optional OpenTelemetry integration
try:
    from opentelemetry import trace as otel_trace
    OTEL_AVAILABLE = True
except ImportError:
    OTEL_AVAILABLE = False


@dataclass
class AutoStreamingSession:
    """Lightweight streaming session for automatic handling."""
    session_id: str
    user_input: str
    model: str
    start_time: float = field(default_factory=time.time)
    chunks: List[str] = field(default_factory=list)
    chunk_count: int = 0
    
    def add_chunk(self, content: str) -> None:
        """Add a chunk to this session."""
        if content:
            self.chunks.append(content)
            self.chunk_count += 1
    
    def get_accumulated_content(self) -> str:
        """Get the full accumulated content."""
        return ''.join(self.chunks)
    
    def get_duration_ms(self) -> float:
        """Get the session duration in milliseconds."""
        return (time.time() - self.start_time) * 1000


class StructuredLogger:
    """
    Structured logger with automatic trace correlation.
    
    This logger automatically includes trace information in log entries
    and formats them as structured JSON for better observability.
    Works with or without OpenTelemetry.
    """
    
    def __init__(self, name: str, service_name: Optional[str] = None, event_context: Optional[str] = None):
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
        
        # Auto-streaming support
        self._streaming_sessions: Dict[str, AutoStreamingSession] = {}
        self._streaming_lock = threading.RLock()
    
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
        kwargs['exc_info'] = True
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
                kwargs['_format_error'] = f"Failed to format message '{message}' with args {args}"
        else:
            formatted_message = message
        
        # Handle auto-streaming if enabled
        should_try_streaming = _auto_streaming_enabled and self._should_handle_streaming(kwargs)
        streaming_handled = False
        
        if should_try_streaming:
            streaming_handled = self._handle_auto_streaming(level, message, kwargs)
            # For user-initiated streaming logs, check if they should go to Loki
            # For internal auto-generated logs, stop here to avoid duplicates
            is_internal_log = kwargs.get("_internal_streaming_log", False)
            if streaming_handled:
                if is_internal_log:
                    return  # Internal streaming log, don't send to Loki
                
                # For user chunk logs, respect the enable_individual_chunk_logging flag
                if self._is_chunk_log(kwargs) and not _enable_individual_chunk_logging:
                    return  # User chunk log but individual logging disabled, don't send to Loki
        
        # Process as regular log (user logs or streaming failures)
        
        # Apply event context if configured
        if self.event_context:
            kwargs = self._apply_event_context(self.event_context, kwargs)
        
        # Get caller information for both JSON and console logs
        caller_info = self._get_caller_info()
        
        # Build structured log entry
        log_entry = {
            'timestamp': time.time(),
            'level': logging.getLevelName(level),
            'message': formatted_message,
            'logger': self.name,
        }
        
        # Add caller information to JSON logs
        if caller_info:
            log_entry.update(caller_info)
        
        # Add service name if available
        if self.service_name:
            log_entry['service'] = self.service_name
        
        # Add trace correlation if OpenTelemetry is available
        if OTEL_AVAILABLE:
            self._add_trace_correlation(log_entry)
        
        # Add any global context
        global_context = get_log_context()
        if global_context:
            log_entry.update(global_context)
        
        # Add custom fields
        for key, value in kwargs.items():
            if key != 'exc_info':  # Skip special logging parameters
                # Flatten nested objects for better readability
                if isinstance(value, dict):
                    for nested_key_str, nested_value in value.items():  # type: ignore
                        log_entry[f"{key}.{nested_key_str}"] = nested_value
                else:
                    log_entry[key] = value
        
        # Log the structured entry
        try:
            if kwargs.get('exc_info'):
                self.logger.log(level, json.dumps(log_entry), exc_info=True)
            else:
                self.logger.log(level, json.dumps(log_entry))
        except json.JSONDecodeError as e:
            self.logger.error(f"Failed to log message: {e}")
            self.logger.info(f"Log entry as message string: \n{log_entry}")
        except Exception as e:
            self.logger.error(f"Failed to log message: {e}")
    
    def _apply_event_context(self, event_type: str, kwargs: Dict[str, Any]) -> Dict[str, Any]:
        """Apply event context and schema filtering to log kwargs."""
        # Filter payload using schema if one is configured
        allowed_fields = _event_schemas.get(event_type)
        if allowed_fields is not None:
            kwargs = {k: v for k, v in kwargs.items() if k in allowed_fields or k == 'exc_info'}
        
        # Add event_type to the log entry
        kwargs['event_type'] = event_type
        
        return kwargs
    
    def _add_trace_correlation(self, log_entry: Dict[str, Any]):
        """Add OpenTelemetry trace correlation if available."""
        try:
            span = otel_trace.get_current_span()
            if span and span.is_recording():
                span_context = span.get_span_context()
                if span_context.is_valid:
                    log_entry['trace_id'] = format(span_context.trace_id, '032x')
                    log_entry['span_id'] = format(span_context.span_id, '016x')
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
                'logging' in frame_filename or
                'logging' in frame_filename or
                'opentelemetry' in frame_filename or
                # Also skip our own logger methods
                frame_function in [
                    '_log', 'log', 'emit', 'handle', 'callHandlers', 
                    'debug', 'info', 'warning', 'error', 'critical', 'exception'
                ]
            ):
                continue
            
            # This is likely the actual caller
            caller_frame = frame_info
            break
        
        # Return caller information as dict
        if caller_frame:
            return {
                'file': os.path.basename(caller_frame.filename),
                'line': caller_frame.lineno,
                'function': caller_frame.function
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
    
    def _is_chunk_log(self, kwargs: Dict[str, Any]) -> bool:
        """Check if this log is a chunk log (has chunk content but no session start indicators)."""
        # Not a chunk if it has session start indicators
        if "user_input" in kwargs and "model" in kwargs:
            return False
        
        # Not a chunk if it's a completion signal
        if "streaming_complete" in kwargs or "stream_end" in kwargs:
            return False
        
        # Check if it has potential chunk content
        if _auto_detect_chunk_fields:
            # Find fields that could be chunk content (not in reserved list)
            potential_chunk_fields = [
                key for key in kwargs.keys()
                if key not in _streaming_reserved_fields and key not in ["streaming_session_id", "streaming_mode"]
            ]
            return len(potential_chunk_fields) > 0
        else:
            # Fallback to traditional field name checking
            field_names = _streaming_field_names
            has_chunk_content = field_names.get("chunk_content", "chunk_content") in kwargs
            return has_chunk_content

    def _should_handle_streaming(self, kwargs: Dict[str, Any]) -> bool:
        """Check if this log should be handled as streaming."""
        # Always handle if streaming completion is signaled
        if "streaming_complete" in kwargs or "stream_end" in kwargs:
            return "streaming_session_id" in kwargs
        
        # Check for explicit streaming mode
        streaming_mode = kwargs.get("streaming_mode", False)
        has_session_id = "streaming_session_id" in kwargs
        
        if not (streaming_mode and has_session_id):
            return False
        
        # Handle session start (has user_input and model)
        if "user_input" in kwargs and "model" in kwargs:
            return True
        
        # If auto-detection is enabled, look for potential chunk content
        if _auto_detect_chunk_fields:
            # Find fields that could be chunk content (not in reserved list)
            potential_chunk_fields = [
                key for key in kwargs.keys()
                if key not in _streaming_reserved_fields and key not in ["streaming_session_id", "streaming_mode"]
            ]
            # If we have potential chunk content, this is a streaming log
            return len(potential_chunk_fields) > 0
        else:
            # Fallback to traditional field name checking
            field_names = _streaming_field_names
            has_chunk_content = field_names.get("chunk_content", "chunk_content") in kwargs
            return has_chunk_content
    
    def _handle_auto_streaming(self, level: int, message: str, kwargs: Dict[str, Any]) -> bool:
        """Handle auto-streaming logic. Returns True if streaming was handled."""
        session_id = kwargs.get("streaming_session_id")
        
        if not session_id:
            return False
        
        with self._streaming_lock:
            # Check if this is a streaming completion signal
            if "streaming_complete" in kwargs or "stream_end" in kwargs:
                return self._finish_streaming_session(session_id, level, message, kwargs)
            
            # Check if this is session start (has user_input and model)
            user_input = kwargs.get("user_input")
            model = kwargs.get("model")
            
            if user_input and model:
                return self._start_streaming_session(session_id, user_input, model, kwargs)
            
            # Find potential chunk content (any field not in reserved list)
            chunk_content = None
            chunk_field_name = None
            
            if _auto_detect_chunk_fields:
                for key, value in kwargs.items():
                    if (key not in _streaming_reserved_fields and 
                        key not in ["streaming_session_id", "streaming_mode"] and
                        isinstance(value, str) and value):  # Only consider non-empty strings
                        chunk_content = value
                        chunk_field_name = key
                        break
            else:
                # Fallback to traditional field name checking
                field_names = _streaming_field_names
                chunk_content = kwargs.get(field_names.get("chunk_content", "chunk_content"))
                chunk_field_name = "chunk_content"
            
            if chunk_content:
                return self._handle_streaming_chunk(session_id, chunk_content, chunk_field_name, kwargs)
        
        return False
    
    def _start_streaming_session(self, session_id: str, user_input: str, model: str, kwargs: Dict[str, Any]) -> bool:
        """Start a new streaming session."""
        if session_id in self._streaming_sessions:
            # Session already exists - log warning using direct logger to avoid recursion
            self.logger.debug(f"Streaming session {session_id} already exists - allowing fallback to regular logging")
            return False  # Session already exists, let original log go through as regular log
        
        session = AutoStreamingSession(
            session_id=session_id,
            user_input=user_input,
            model=model
        )
        self._streaming_sessions[session_id] = session
        
        # Log session start (optional, can be disabled)
        self.debug(f"Auto-streaming session started: {session_id}",
                  session_id=session_id,
                  user_input=user_input,
                  model=model,
                  streaming_mode=True,
                  event_type="streaming_start",
                  _internal_streaming_log=True)
        
        return True
    
    def _handle_streaming_chunk(self, session_id: str, chunk_content: str, chunk_field_name: str, kwargs: Dict[str, Any]) -> bool:
        """Handle a streaming chunk."""
        session = self._streaming_sessions.get(session_id)
        if not session:
            # Session should have been created by start_streaming_session first
            # If no session exists, log a warning and skip this chunk
            self.warning(f"Received chunk for unknown session: {session_id}",
                        session_id=session_id,
                        chunk_field_used=chunk_field_name,
                        chunk_content=chunk_content[:50])  # Only show first 50 chars
            return False
        
        session.add_chunk(chunk_content)
        
        # Log individual chunk only if enabled
        if _enable_individual_chunk_logging:
            self.debug(f"Streaming chunk received",
                      session_id=session_id,
                      chunk_number=session.chunk_count,
                      chunk_field_used=chunk_field_name,  # Show which field was detected as chunk content
                      chunk_content=chunk_content,
                      chunk_length=len(chunk_content),
                      accumulated_length=len(session.get_accumulated_content()),
                      model=session.model,
                      streaming_mode=True,
                      event_type="streaming_chunk",
                      _internal_streaming_log=True)
        
        return True
    
    def _finish_streaming_session(self, session_id: str, level: int, message: str, kwargs: Dict[str, Any]) -> bool:
        """Finish a streaming session and send aggregated log."""
        session = self._streaming_sessions.pop(session_id, None)
        if not session:
            return False
        
        accumulated_content = session.get_accumulated_content()
        duration_ms = session.get_duration_ms()
        
        # Build final aggregated log with configurable field names
        final_log_data = {
            "streaming_session_id": session_id,
            "user_input": session.user_input,
            _accumulated_content_field_name: accumulated_content,  # Use configurable field name
            "total_chunks": session.chunk_count,
            "model": session.model,
            "streaming_mode": True,
            "accumulated_length": len(accumulated_content),
            "duration_ms": duration_ms,
            "event_type": "streaming_complete"
        }
        
        # Add any additional fields from the completion kwargs
        for key, value in kwargs.items():
            if key not in ["streaming_complete", "stream_end", "streaming_session_id"]:
                final_log_data[key] = value
        
        # Send final aggregated log
        self._log_final_streaming_result(level, f"Streaming session completed: {session_id}", final_log_data)
        
        return True
    
    def _log_final_streaming_result(self, level: int, message: str, log_data: Dict[str, Any]):
        """Log the final streaming result without triggering streaming logic again."""
        # Apply event context if configured
        if self.event_context:
            log_data = self._apply_event_context(self.event_context, log_data)
        
        # Build structured log entry
        log_entry = {
            'timestamp': time.time(),
            'level': logging.getLevelName(level),
            'message': message,
            'logger': self.name,
        }
        
        # Add service name if available
        if self.service_name:
            log_entry['service'] = self.service_name
        
        # Add trace correlation if OpenTelemetry is available
        if OTEL_AVAILABLE:
            self._add_trace_correlation(log_entry)
        
        # Add any global context
        global_context = get_log_context()
        if global_context:
            log_entry.update(global_context)
        
        # Add streaming data
        log_entry.update(log_data)
        
        # Log the structured entry
        self.logger.log(level, json.dumps(log_entry))


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

# Global auto-streaming configuration
_auto_streaming_enabled: bool = False
_streaming_field_names: Dict[str, str] = {}
_auto_detect_chunk_fields: bool = True
_accumulated_content_field_name: str = "accumulated_content"
_enable_individual_chunk_logging: bool = False
_streaming_reserved_fields: List[str] = []


def get_logger(name: str, service_name: Optional[str] = None, event_context: Optional[str] = None) -> StructuredLogger:
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
        # This will automatically include event_type="langgraph" and apply schema filtering
    """
    effective_service_name = service_name or _global_service_name
    effective_event_context = event_context or _global_event_context
    cache_key = f"{name}:{effective_service_name}:{effective_event_context}"
    
    if cache_key not in _loggers:
        _loggers[cache_key] = StructuredLogger(name, effective_service_name, effective_event_context)
    
    return _loggers[cache_key]


def setup_logging(
    service_name: str,
    level: str = "INFO",
    format_json: bool = True,
    loki_endpoint: Optional[str] = None,
    environment: Optional[str] = None
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
    logger.debug("Logging system initialized", 
                service=service_name, 
                log_level=level,
                json_format=format_json,
                otel_available=OTEL_AVAILABLE)


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
        format='%(message)s' if format_json else '%(asctime)s - %(name)s - %(levelname)s - %(message)s',
        datefmt='%Y-%m-%d %H:%M:%S'
    )
    
    # Disable some noisy loggers
    logging.getLogger('urllib3').setLevel(logging.WARNING)
    logging.getLogger('requests').setLevel(logging.WARNING)
    logging.getLogger('opentelemetry').setLevel(logging.WARNING)


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


def configure_auto_streaming(
    enabled: bool, 
    auto_detect_chunk_fields: bool = True,
    accumulated_content_field_name: str = "accumulated_content",
    enable_individual_chunk_logging: bool = False,
    streaming_reserved_fields: Optional[List[str]] = None,
    field_names: Optional[Dict[str, str]] = None
) -> None:
    """Configure auto-streaming behavior for all loggers.
    
    Args:
        enabled: Whether to enable auto-streaming
        auto_detect_chunk_fields: Whether to automatically detect any field as chunk content
        accumulated_content_field_name: Field name for the final accumulated content
        enable_individual_chunk_logging: Whether to log individual chunks
        streaming_reserved_fields: List of field names that won't be treated as chunk content
        field_names: Optional mapping of field names for streaming logs (backward compatibility)
    """
    global _auto_streaming_enabled, _streaming_field_names, _auto_detect_chunk_fields
    global _accumulated_content_field_name, _enable_individual_chunk_logging, _streaming_reserved_fields
    
    _auto_streaming_enabled = enabled
    _auto_detect_chunk_fields = auto_detect_chunk_fields
    _accumulated_content_field_name = accumulated_content_field_name
    _enable_individual_chunk_logging = enable_individual_chunk_logging
    
    if streaming_reserved_fields:
        _streaming_reserved_fields = streaming_reserved_fields.copy()
    else:
        # Set default reserved fields
        _streaming_reserved_fields = [
            "streaming_session_id", "streaming_mode", "streaming_complete", "stream_end",
            "user_input", "model", "chunk_number", "chunk_length", "timestamp",
            "level", "message", "logger", "service", "environment", "hostname", 
            "run_id", "event_type", "exc_info", "total_chunks", "duration_ms",
            "accumulated_length"
        ]
    
    if field_names:
        _streaming_field_names = field_names.copy()
    else:
        # Set default field names (for backward compatibility)
        _streaming_field_names = {
            "user_input": "user_input",
            "model": "model",
            "streaming_mode": "streaming_mode",
            "streaming_session_id": "streaming_session_id",
            "total_chunks": "total_chunks"
        }


def is_auto_streaming_enabled() -> bool:
    """Check if auto-streaming is enabled."""
    return _auto_streaming_enabled


def get_accumulated_content_for_session(session_id: str) -> Optional[str]:
    """
    Get the accumulated content for a specific streaming session.
    
    This is useful when you want to access the accumulated content
    before the session is automatically completed.
    
    Args:
        session_id: The session ID to get content for
        
    Returns:
        The accumulated content as a string, or None if session doesn't exist
    """
    # Find the logger instance that has this session
    # We'll iterate through all active StructuredLogger instances
    for logger_instance in _get_all_logger_instances():
        if hasattr(logger_instance, '_streaming_sessions'):
            session = logger_instance._streaming_sessions.get(session_id)
            if session:
                return session.get_accumulated_content()
    return None


def _get_all_logger_instances():
    """Helper to get all active StructuredLogger instances."""
    # This is a simple approach - in a more complex system, you might want
    # to maintain a registry of logger instances
    import gc
    return [obj for obj in gc.get_objects() if isinstance(obj, StructuredLogger)] 