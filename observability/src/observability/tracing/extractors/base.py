"""
Base classes for attribute extractors.

This module defines the interface that all attribute extractors must implement.
Extractors are responsible for understanding different types of operations and
extracting relevant telemetry attributes from function calls.
"""

from abc import ABC, abstractmethod
from typing import Any, Callable, Dict, Tuple


class AttributeExtractor(ABC):
    """
    Base class for extracting attributes from function calls.

    Extractors provide framework-specific intelligence for different types of operations
    (HTTP requests, database queries, RPC calls, etc.) without coupling the core
    observability functionality to specific frameworks.

    To create a custom extractor, inherit from this class and implement the abstract
    methods.
    """

    @abstractmethod
    def extract_attributes(
        self, func: Callable, args: Tuple, kwargs: Dict[str, Any]
    ) -> Dict[str, Any]:
        """
        Extract span attributes from a function call.

        Args:
            func: The function being called
            args: Positional arguments passed to the function
            kwargs: Keyword arguments passed to the function

        Returns:
            Dictionary of attributes to add to the trace span

        Example:
            {
                "http.method": "POST",
                "http.url": "/api/users",
                "http.status_code": 200
            }
        """
        pass

    @abstractmethod
    def get_span_name(self, func: Callable, args: Tuple, kwargs: Dict[str, Any]) -> str:
        """
        Generate a span name for the operation.

        Args:
            func: The function being called
            args: Positional arguments passed to the function
            kwargs: Keyword arguments passed to the function

        Returns:
            String to use as the span name

        Example:
            "HTTP POST /api/users"
        """
        pass

    def get_metrics_labels(
        self, func: Callable, args: Tuple, kwargs: Dict[str, Any]
    ) -> Dict[str, str]:
        """
        Generate labels for metrics collection.

        Args:
            func: The function being called
            args: Positional arguments passed to the function
            kwargs: Keyword arguments passed to the function

        Returns:
            Dictionary of labels to add to metrics

        Example:
            {
                "operation": "create_user",
                "method": "POST"
            }
        """
        return {"operation": func.__name__}

    def extract_error_attributes(
        self, func: Callable, args: Tuple, kwargs: Dict[str, Any], exception: Exception
    ) -> Dict[str, Any]:
        """
        Extract additional attributes when an operation fails.

        Args:
            func: The function that failed
            args: Positional arguments passed to the function
            kwargs: Keyword arguments passed to the function
            exception: The exception that was raised

        Returns:
            Dictionary of error-specific attributes

        Example:
            {
                "error.type": "ValidationError",
                "error.message": "Invalid email format"
            }
        """
        return {
            "error.type": type(exception).__name__,
            "error.message": str(exception),
        }


class NoOpExtractor(AttributeExtractor):
    """
    A no-op extractor that provides minimal functionality.

    This is used as a fallback when no specific extractor is provided.
    """

    def extract_attributes(
        self, func: Callable, args: Tuple, kwargs: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Return basic function information."""
        return {
            "function.name": func.__name__,
            "function.module": func.__module__,
        }

    def get_span_name(self, func: Callable, args: Tuple, kwargs: Dict[str, Any]) -> str:
        """Return function name as span name."""
        return func.__name__

    def get_metrics_labels(
        self, func: Callable, args: Tuple, kwargs: Dict[str, Any]
    ) -> Dict[str, str]:
        """Return basic function labels."""
        return {"operation": func.__name__, "module": func.__module__ or "unknown"}
