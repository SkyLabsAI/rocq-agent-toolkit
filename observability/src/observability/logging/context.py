"""
Context management for structured logging.

Provides utilities to add temporary context to log entries,
useful for request-scoped or operation-scoped logging context.
"""

from contextlib import contextmanager
from typing import Any, Dict, Optional
from .core import add_log_context, get_log_context, clear_log_context


@contextmanager
def log_context(**context):
    """
    Context manager to temporarily add logging context.
    
    Args:
        **context: Key-value pairs to add to logging context
        
    Example:
        with log_context(request_id="abc123", user_id="user456"):
            logger.info("Processing request")  # Includes request_id and user_id
            do_some_work()
    """
    # Save current context
    original_context = get_log_context()
    
    try:
        # Add new context
        for key, value in context.items():
            add_log_context(key, value)
        
        yield
    finally:
        # Restore original context
        clear_log_context()
        for key, value in original_context.items():
            add_log_context(key, value) 