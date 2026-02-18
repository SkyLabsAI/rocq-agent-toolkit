"""
Core observability decorators.

This module provides the main @trace decorator that works with any operation type
through the extractor system. It replaces all framework-specific decorators with
a single, unified, generic approach.
"""

import functools
import logging
import time
from collections.abc import Awaitable, Callable, Coroutine
from typing import Any

from opentelemetry import metrics
from opentelemetry import trace as otel_trace
from opentelemetry.trace import Status, StatusCode

from .extractors import get_extractor
from .extractors.base import AttributeExtractor, NoOpExtractor

logger = logging.getLogger(__name__)


def trace[**P, T](
    name: str | None = None,
    *,
    extractor: str | type[AttributeExtractor] | AttributeExtractor | None = None,
    attributes: dict[str, Any] | None = None,
    metrics_enabled: bool = True,
    include_args: bool = False,
    include_result: bool = False,
    record_exception: bool = True,
    **extractor_kwargs: Any,
) -> Callable[[Callable[P, T]], Callable[P, T]]:
    """
    Universal tracing decorator for any operation.

    This decorator provides comprehensive observability for any Python function by:
    - Creating distributed tracing spans
    - Recording metrics automatically
    - Using extractors for framework-specific intelligence
    - Supporting custom attributes and labels

    Args:
        name: Custom span name (defaults to extractor's name generation)
        extractor: Attribute extractor to use:
                  - String: "http", "rpc", "database", "workflow", "custom"
                  - Class: CustomExtractor class
                  - Instance: Pre-configured extractor instance
        attributes: Static attributes to add to all spans
        metrics_enabled: Whether to record operation metrics
        include_args: Include function arguments in span(be careful with sensitive data)
        include_result: Include function result in span (be careful with sensitive data)
        record_exception: Whether to record exceptions in spans
        **extractor_kwargs: Arguments passed to extractor constructor

    Returns:
        Decorated function with observability

    Examples:
        # Basic tracing
        @trace()
        def my_function():
            return "result"

        # HTTP endpoint
        @trace(extractor="http")
        def create_user(request):
            return {"user_id": "123"}

        # Database operation
        @trace(extractor="database", system="postgresql", table="users")
        def get_user(user_id):
            return db.query("SELECT * FROM users WHERE id = %s", user_id)

        # RPC method
        @trace("CreateUser", extractor="rpc", system="grpc")
        def CreateUser(self, request, context):
            return user_pb2.UserResponse(user_id="123")

        # Workflow step
        @trace(extractor="workflow", workflow_type="user_onboarding")
        def validate_email(state):
            state['email_valid'] = validate(state['email'])
            return state

        # Custom operation with business context
        @trace(extractor=CustomExtractor(
            operation_type="payment_processing",
            attributes={"payment.provider": "stripe"}
        ))
        def process_payment(amount, currency):
            return stripe.charge(amount, currency)
    """

    def decorator(func: Callable[P, T]) -> Callable[P, T]:
        @functools.wraps(func)
        def wrapper(*args: P.args, **kwargs: P.kwargs) -> T:
            # Initialize extractor
            operation_extractor = _get_operation_extractor(
                extractor, **extractor_kwargs
            )

            # Generate span name
            span_name = name
            if not span_name:
                try:
                    span_name = operation_extractor.get_span_name(func, args, kwargs)
                except Exception as e:
                    logger.warning(f"Failed to generate span name: {e}")
                    span_name = func.__name__

            # Get tracer and start timing
            tracer = otel_trace.get_tracer(__name__)
            start_time = time.time()

            with tracer.start_as_current_span(span_name) as span:
                try:
                    # Extract and set basic attributes
                    _set_basic_attributes(span, func, args, kwargs, include_args)

                    # Add custom attributes
                    if attributes:
                        _set_custom_attributes(span, attributes)

                    # Use extractor for framework-specific attributes
                    _set_extractor_attributes(
                        span, operation_extractor, func, args, kwargs
                    )

                    # Record metrics start
                    if metrics_enabled:
                        _record_start_metrics(operation_extractor, func, args, kwargs)

                    # Execute the function
                    result = func(*args, **kwargs)

                    # Record result if requested
                    if include_result:
                        _set_result_attributes(span, result)

                    # Record success metrics
                    duration = time.time() - start_time
                    if metrics_enabled:
                        _record_success_metrics(
                            operation_extractor, func, args, kwargs, duration
                        )

                    # Mark span as successful
                    span.set_status(Status(StatusCode.OK))
                    return result

                except Exception as e:
                    # Record exception
                    duration = time.time() - start_time

                    if record_exception:
                        span.record_exception(e)
                        span.set_status(Status(StatusCode.ERROR, str(e)))

                        # Add extractor-specific error attributes
                        try:
                            error_attrs = operation_extractor.extract_error_attributes(
                                func, args, kwargs, e
                            )
                            _set_custom_attributes(span, error_attrs)
                        except Exception as extractor_error:
                            logger.warning(
                                f"Failed to extract error attributes: {extractor_error}"
                            )

                    # Record error metrics
                    if metrics_enabled:
                        _record_error_metrics(
                            operation_extractor, func, args, kwargs, duration, e
                        )

                    raise

        return wrapper

    return decorator


def trace_async[**P, T](
    name: str | None = None,
    *,
    extractor: str | type[AttributeExtractor] | AttributeExtractor | None = None,
    attributes: dict[str, Any] | None = None,
    metrics_enabled: bool = True,
    include_args: bool = False,
    include_result: bool = False,
    record_exception: bool = True,
    **extractor_kwargs: Any,
) -> Callable[[Callable[P, Awaitable[T]]], Callable[P, Coroutine[Any, Any, T]]]:
    """
    Universal tracing decorator for any async operation.

    See the documentation of `trace` for more information.
    """

    def decorator(
        func: Callable[P, Awaitable[T]],
    ) -> Callable[P, Coroutine[Any, Any, T]]:
        @functools.wraps(func)
        async def wrapper(*args: P.args, **kwargs: P.kwargs) -> T:
            # Initialize extractor
            operation_extractor = _get_operation_extractor(
                extractor, **extractor_kwargs
            )

            # Generate span name
            span_name = name
            if not span_name:
                try:
                    span_name = operation_extractor.get_span_name(func, args, kwargs)
                except Exception as e:
                    logger.warning(f"Failed to generate span name: {e}")
                    span_name = func.__name__

            # Get tracer and start timing
            tracer = otel_trace.get_tracer(__name__)
            start_time = time.time()

            with tracer.start_as_current_span(span_name) as span:
                try:
                    # Extract and set basic attributes
                    _set_basic_attributes(span, func, args, kwargs, include_args)

                    # Add custom attributes
                    if attributes:
                        _set_custom_attributes(span, attributes)

                    # Use extractor for framework-specific attributes
                    _set_extractor_attributes(
                        span, operation_extractor, func, args, kwargs
                    )

                    # Record metrics start
                    if metrics_enabled:
                        _record_start_metrics(operation_extractor, func, args, kwargs)

                    # Execute the function
                    result = await func(*args, **kwargs)

                    # Record result if requested
                    if include_result:
                        _set_result_attributes(span, result)

                    # Record success metrics
                    duration = time.time() - start_time
                    if metrics_enabled:
                        _record_success_metrics(
                            operation_extractor, func, args, kwargs, duration
                        )

                    # Mark span as successful
                    span.set_status(Status(StatusCode.OK))
                    return result

                except Exception as e:
                    # Record exception
                    duration = time.time() - start_time

                    if record_exception:
                        span.record_exception(e)
                        span.set_status(Status(StatusCode.ERROR, str(e)))

                        # Add extractor-specific error attributes
                        try:
                            error_attrs = operation_extractor.extract_error_attributes(
                                func, args, kwargs, e
                            )
                            _set_custom_attributes(span, error_attrs)
                        except Exception as extractor_error:
                            logger.warning(
                                f"Failed to extract error attributes: {extractor_error}"
                            )

                    # Record error metrics
                    if metrics_enabled:
                        _record_error_metrics(
                            operation_extractor, func, args, kwargs, duration, e
                        )

                    raise

        return wrapper

    return decorator


def _get_operation_extractor(extractor_spec: Any, **kwargs: Any) -> AttributeExtractor:
    """Get the appropriate extractor instance."""
    if extractor_spec is None:
        return NoOpExtractor()

    try:
        return get_extractor(extractor_spec, **kwargs)
    except Exception as e:
        logger.warning(
            f"Failed to create extractor {extractor_spec}: {e}. Using NoOpExtractor."
        )
        return NoOpExtractor()


def _set_basic_attributes(
    span: Any, func: Callable, args: tuple, kwargs: dict, include_args: bool
) -> None:
    """Set basic function attributes on the span."""
    span.set_attribute("function.name", func.__name__)
    span.set_attribute("function.module", func.__module__ or "unknown")

    # Add argument information if requested
    if include_args:
        span.set_attribute("function.args.count", len(args))
        span.set_attribute("function.kwargs.count", len(kwargs))

        # Add argument names (be careful not to include values for security)
        if hasattr(func, "__code__"):
            arg_names = func.__code__.co_varnames[: func.__code__.co_argcount]
            if arg_names:
                span.set_attribute("function.args.names", ",".join(arg_names))


def _set_custom_attributes(span: Any, attributes: dict[str, Any]) -> None:
    """Set custom attributes on the span."""
    for key, value in attributes.items():
        if value is not None:
            # Convert to string and limit length
            str_value = str(value)
            if len(str_value) > 1000:
                str_value = str_value[:1000] + "..."
            span.set_attribute(key, str_value)


def _set_extractor_attributes(
    span: Any, extractor: AttributeExtractor, func: Callable, args: tuple, kwargs: dict
) -> None:
    """Extract and set attributes using the operation extractor."""
    try:
        extracted_attrs = extractor.extract_attributes(func, args, kwargs)
        _set_custom_attributes(span, extracted_attrs)
    except Exception as e:
        logger.warning(f"Failed to extract attributes: {e}")
        # Continue operation even if attribute extraction fails


def _set_result_attributes(span: Any, result: Any) -> None:
    """Set attributes based on function result."""
    span.set_attribute("function.result.type", type(result).__name__)

    # Add result size if possible
    if hasattr(result, "__len__"):
        try:
            span.set_attribute("function.result.size", len(result))
        except Exception:
            pass

    # Add result value (be very careful with this)
    if result is not None:
        result_str = str(result)
        if len(result_str) <= 200:  # Only include small results
            span.set_attribute("function.result.value", result_str)


def _record_start_metrics(
    extractor: AttributeExtractor, func: Callable, args: tuple, kwargs: dict
) -> None:
    """Record metrics when operation starts."""
    try:
        meter = metrics.get_meter(__name__)

        # Get labels from extractor
        labels = extractor.get_metrics_labels(func, args, kwargs)

        # Increment operation counter
        operation_counter = meter.create_counter(
            name="operation_total", description="Total number of operations", unit="1"
        )
        operation_counter.add(1, {**labels, "status": "started"})

    except Exception as e:
        logger.warning(f"Failed to record start metrics: {e}")


def _record_success_metrics(
    extractor: AttributeExtractor,
    func: Callable,
    args: tuple,
    kwargs: dict,
    duration: float,
) -> None:
    """Record metrics for successful operations."""
    try:
        meter = metrics.get_meter(__name__)

        # Get labels from extractor
        labels = extractor.get_metrics_labels(func, args, kwargs)

        # Record success counter
        operation_counter = meter.create_counter(
            name="operation_total", description="Total number of operations", unit="1"
        )
        operation_counter.add(1, {**labels, "status": "success"})

        # Record duration
        operation_duration = meter.create_histogram(
            name="operation_duration_seconds",
            description="Duration of operations in seconds",
            unit="s",
        )
        operation_duration.record(duration, {**labels, "status": "success"})

    except Exception as e:
        logger.warning(f"Failed to record success metrics: {e}")


def _record_error_metrics(
    extractor: AttributeExtractor,
    func: Callable,
    args: tuple,
    kwargs: dict,
    duration: float,
    exception: Exception,
) -> None:
    """Record metrics for failed operations."""
    try:
        meter = metrics.get_meter(__name__)

        # Get labels from extractor
        labels = extractor.get_metrics_labels(func, args, kwargs)
        error_labels = {
            **labels,
            "status": "error",
            "error_type": type(exception).__name__,
        }

        # Record error counter
        operation_counter = meter.create_counter(
            name="operation_total", description="Total number of operations", unit="1"
        )
        operation_counter.add(1, error_labels)

        # Record duration for failed operations too
        operation_duration = meter.create_histogram(
            name="operation_duration_seconds",
            description="Duration of operations in seconds",
            unit="s",
        )
        operation_duration.record(duration, error_labels)

    except Exception as e:
        logger.warning(f"Failed to record error metrics: {e}")


# Convenience aliases for common patterns
def trace_http(**kwargs: Any) -> Callable:
    """Convenience decorator for HTTP operations."""
    return trace(extractor="http", **kwargs)


def trace_rpc(**kwargs: Any) -> Callable:
    """Convenience decorator for RPC operations."""
    return trace(extractor="rpc", **kwargs)


def trace_database(**kwargs: Any) -> Callable:
    """Convenience decorator for database operations."""
    return trace(extractor="database", **kwargs)


def trace_workflow(**kwargs: Any) -> Callable:
    """Convenience decorator for workflow operations."""
    return trace(extractor="workflow", **kwargs)


def trace_langchain(**kwargs: Any) -> Callable:
    """Convenience decorator for LangChain/LangGraph operations."""
    return trace(extractor="langchain", **kwargs)
