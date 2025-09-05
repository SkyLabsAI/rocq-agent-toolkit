"""
Event-based logging for business and operational events.

This module provides high-level logging functions for common
event types that need consistent structure across services.
"""

from typing import Any, Dict, Optional
from .core import get_logger


def log_operation_start(operation: str, **kwargs):
    """
    Log the start of an operation.
    
    Args:
        operation: Name of the operation
        **kwargs: Additional context
        
    Example:
        log_operation_start("user_registration", user_id="123", source="web")
    """
    logger = get_logger("events.operations")
    logger.info(f"Operation started: {operation}", 
                operation=operation, 
                event="operation_start", 
                **kwargs)


def log_operation_success(operation: str, duration_ms: Optional[float] = None, **kwargs):
    """
    Log successful completion of an operation.
    
    Args:
        operation: Name of the operation
        duration_ms: Operation duration in milliseconds
        **kwargs: Additional context
        
    Example:
        log_operation_success("user_registration", duration_ms=250, user_id="123")
    """
    logger = get_logger("events.operations")
    log_data = {"operation": operation, "event": "operation_success"}
    if duration_ms is not None:
        log_data["duration_ms"] = duration_ms
    log_data.update(kwargs)
    
    logger.info(f"Operation completed: {operation}", **log_data)


def log_operation_error(operation: str, error: str, duration_ms: Optional[float] = None, **kwargs):
    """
    Log an operation error.
    
    Args:
        operation: Name of the operation
        error: Error description
        duration_ms: Operation duration in milliseconds
        **kwargs: Additional context
        
    Example:
        log_operation_error("user_registration", "Email already exists", 
                           duration_ms=100, user_email="test@example.com")
    """
    logger = get_logger("events.operations")
    log_data = {
        "operation": operation, 
        "event": "operation_error",
        "error": error
    }
    if duration_ms is not None:
        log_data["duration_ms"] = duration_ms
    log_data.update(kwargs)
    
    logger.error(f"Operation failed: {operation}", **log_data)


def log_business_event(event_type: str, event_data: Optional[Dict[str, Any]] = None, **kwargs):
    """
    Log a business event.
    
    Args:
        event_type: Type of business event
        event_data: Structured event data
        **kwargs: Additional context
        
    Example:
        log_business_event("user_signup", {
            "plan": "premium",
            "source": "web",
            "trial_days": 14
        }, user_id="123")
    """
    logger = get_logger("events.business")
    log_data = {"event_type": event_type, "event": "business_event"}
    
    if event_data:
        log_data["event_data"] = event_data
    
    log_data.update(kwargs)
    
    logger.info(f"Business event: {event_type}", **log_data)


def log_security_event(event_type: str, severity: str = "info", **kwargs):
    """
    Log a security-related event.
    
    Args:
        event_type: Type of security event
        severity: Security severity (info, warning, critical)
        **kwargs: Additional context
        
    Example:
        log_security_event("login_failed", severity="warning", 
                          ip="192.168.1.1", user_email="test@example.com")
    """
    logger = get_logger("events.security")
    log_data = {
        "event_type": event_type,
        "event": "security_event", 
        "security_severity": severity
    }
    log_data.update(kwargs)
    
    # Map severity to log level
    if severity == "critical":
        logger.critical(f"Security event: {event_type}", **log_data)
    elif severity == "warning":
        logger.warning(f"Security event: {event_type}", **log_data)
    else:
        logger.info(f"Security event: {event_type}", **log_data)


def log_performance_metric(metric_name: str, value: float, unit: str = "", **kwargs):
    """
    Log a performance metric.
    
    Args:
        metric_name: Name of the metric
        value: Metric value
        unit: Metric unit (ms, seconds, bytes, etc.)
        **kwargs: Additional context
        
    Example:
        log_performance_metric("db_query_time", 45.2, "ms", 
                              query_type="user_lookup")
    """
    logger = get_logger("events.performance")
    log_data = {
        "metric_name": metric_name,
        "metric_value": value,
        "event": "performance_metric"
    }
    
    if unit:
        log_data["metric_unit"] = unit
    
    log_data.update(kwargs)
    
    logger.info(f"Performance metric: {metric_name}={value}{unit}", **log_data)


def log_api_request(method: str, path: str, status_code: int, duration_ms: float, **kwargs):
    """
    Log an API request.
    
    Args:
        method: HTTP method
        path: Request path
        status_code: Response status code
        duration_ms: Request duration in milliseconds
        **kwargs: Additional context
        
    Example:
        log_api_request("POST", "/api/users", 201, 156.7, 
                       user_id="123", request_size=1024)
    """
    logger = get_logger("events.api")
    log_data = {
        "http_method": method,
        "http_path": path,
        "http_status_code": status_code,
        "duration_ms": duration_ms,
        "event": "api_request"
    }
    log_data.update(kwargs)
    
    if status_code >= 500:
        logger.error(f"API request: {method} {path} -> {status_code}", **log_data)
    elif status_code >= 400:
        logger.warning(f"API request: {method} {path} -> {status_code}", **log_data)
    else:
        logger.info(f"API request: {method} {path} -> {status_code}", **log_data)


def log_user_action(user_id: str, action: str, **kwargs):
    """
    Log a user action for analytics/audit.
    
    Args:
        user_id: User identifier
        action: Action performed
        **kwargs: Additional context
        
    Example:
        log_user_action("user123", "profile_updated", 
                       fields_changed=["email", "name"])
    """
    logger = get_logger("events.user_actions")
    log_data = {
        "user_id": user_id,
        "user_action": action,
        "event": "user_action"
    }
    log_data.update(kwargs)
    
    logger.info(f"User action: {action}", **log_data) 