"""
Context managers for manual observability instrumentation.

This module provides context managers for cases where decorators are not appropriate,
such as instrumenting parts of functions, dynamic operations, or complex control flow.
"""

import logging
import time
from collections.abc import Iterator
from contextlib import contextmanager
from typing import Any

from opentelemetry import metrics, trace
from opentelemetry.trace import Span, Status, StatusCode

from .extractors import get_extractor
from .extractors.base import AttributeExtractor, NoOpExtractor

logger = logging.getLogger(__name__)


@contextmanager
def trace_context(
    name: str,
    *,
    extractor: str | type[AttributeExtractor] | AttributeExtractor | None = None,
    tracer_kwargs: dict[str, Any] | None = None,
    attributes: dict[str, Any] | None = None,
    metrics_enabled: bool = True,
    record_exception: bool = True,
    **extractor_kwargs: Any,
) -> Iterator[Span]:
    """
    Context manager for manual tracing of code blocks.

    Use this when you need to trace specific parts of a function or when
    decorators are not appropriate.

    Args:
        name: Name for the span
        extractor: Attribute extractor to use (same options as @trace decorator)
        tracer_kwargs: Custom arguments for tracer.start_as_current_span
        attributes: Static attributes to add to the span
        metrics_enabled: Whether to record metrics
        record_exception: Whether to record exceptions
        **extractor_kwargs: Arguments passed to extractor constructor

    Yields:
        Span object that can be used to add additional attributes or events

    Examples:
        # Basic usage
        with trace_context("data_processing") as span:
            results = process_large_dataset()
            span.set_attribute("processed_records", len(results))

        # With extractor
        with trace_context("db_transaction", extractor="database", system="postgresql")
        as span:
            user = create_user(user_data)
            span.set_attribute("user.id", user.id)

            profile = create_profile(user.id, profile_data)
            span.set_attribute("profile.created", True)

        # Nested operations
        with trace_context("user_onboarding", extractor="workflow") as parent_span:
            user = create_user(user_data)
            parent_span.set_attribute("user.id", user.id)

            with trace_context("send_welcome_email", extractor="http") as email_span:
                send_email(user.email, "welcome")
                email_span.set_attribute("email.template", "welcome")
    """
    # Initialize extractor
    operation_extractor = _get_operation_extractor(extractor, **extractor_kwargs)

    # Get tracer
    tracer = trace.get_tracer(__name__)
    start_time = time.time()

    if tracer_kwargs is None:
        tracer_kwargs = {}

    with tracer.start_as_current_span(name, **tracer_kwargs) as span:
        try:
            # Set basic attributes
            span.set_attribute("operation.type", "manual")
            span.set_attribute("operation.name", name)

            # Add custom attributes
            if attributes:
                _set_custom_attributes(span, attributes)

            # Record metrics start
            if metrics_enabled:
                _record_context_start_metrics(operation_extractor, name)

            yield span

            # Record success metrics
            duration = time.time() - start_time
            if metrics_enabled:
                _record_context_success_metrics(operation_extractor, name, duration)

            # Mark span as successful
            span.set_status(Status(StatusCode.OK))

        except Exception as e:
            duration = time.time() - start_time

            if record_exception:
                span.record_exception(e)
                span.set_status(Status(StatusCode.ERROR, str(e)))

            # Record error metrics
            if metrics_enabled:
                _record_context_error_metrics(operation_extractor, name, duration, e)

            raise


def get_current_span() -> Span | None:
    """
    Get the current active span.

    This is useful for adding attributes or events to the current span
    from within traced functions.

    Returns:
        Current span if one is active, None otherwise

    Example:
        @trace(extractor="database")
        def complex_database_operation():
            # Get current span to add dynamic attributes
            span = get_current_span()

            records = query_database()
            if span:
                span.set_attribute("records.found", len(records))
                span.add_event("Database query completed")

            processed = process_records(records)
            if span:
                span.set_attribute("records.processed", len(processed))
                span.add_event("Record processing completed")

            return processed
    """
    return trace.get_current_span()


def add_span_event(name: str, attributes: dict[str, Any] | None = None) -> None:
    """
    Add an event to the current span.

    Events represent interesting points in time during a span's lifetime.

    Args:
        name: Name of the event
        attributes: Optional attributes for the event

    Example:
        @trace(extractor="workflow")
        def process_order(order):
            validate_order(order)
            add_span_event("Order validated")

            payment = process_payment(order.total)
            add_span_event("Payment processed", {"payment.id": payment.id})

            ship_order(order)
            add_span_event("Order shipped")
    """
    span = get_current_span()
    if span and span.is_recording():
        span.add_event(name, attributes or {})


def set_span_attribute(key: str, value: Any) -> None:
    """
    Set an attribute on the current span.

    Args:
        key: Attribute key
        value: Attribute value

    Example:
        @trace(extractor="http")
        def process_request(request):
            user = authenticate_user(request)
            set_span_attribute("user.id", user.id)
            set_span_attribute("user.role", user.role)

            result = handle_request(request, user)
            set_span_attribute("response.size", len(result))

            return result
    """
    span = get_current_span()
    if span and span.is_recording():
        # Convert value to string and limit length
        str_value = str(value)
        if len(str_value) > 1000:
            str_value = str_value[:1000] + "..."
        span.set_attribute(key, str_value)


@contextmanager
def suppress_tracing() -> Any:
    """
    Context manager to suppress tracing for a block of code.

    This is useful when you want to prevent certain operations from
    creating spans (e.g., internal utility functions, health checks).

    Example:
        @trace(extractor="http")
        def api_endpoint(request):
            # This will be traced
            user = authenticate_user(request)

            with suppress_tracing():
                # This internal logging won't create spans
                log_user_activity(user.id)
                update_metrics(request.path)

            # This will be traced again
            return process_request(request, user)
    """
    # Get the current tracer
    _ = trace.get_tracer(__name__)  # noqa: F841

    # Create a no-op tracer context
    with trace.use_span(trace.INVALID_SPAN):
        yield


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


def _set_custom_attributes(span: Span, attributes: dict[str, Any]) -> None:
    """Set custom attributes on the span."""
    for key, value in attributes.items():
        if value is not None:
            # Convert to string and limit length
            str_value = str(value)
            if len(str_value) > 1000:
                str_value = str_value[:1000] + "..."
            span.set_attribute(key, str_value)


def _record_context_start_metrics(
    extractor: AttributeExtractor, operation_name: str
) -> None:
    """Record metrics when context operation starts."""
    try:
        meter = metrics.get_meter(__name__)

        # Create basic labels
        labels = {"operation": operation_name, "operation_type": "manual"}

        # Increment operation counter
        operation_counter = meter.create_counter(
            name="operation_total", description="Total number of operations", unit="1"
        )
        operation_counter.add(1, {**labels, "status": "started"})

    except Exception as e:
        logger.warning(f"Failed to record context start metrics: {e}")


def _record_context_success_metrics(
    extractor: AttributeExtractor, operation_name: str, duration: float
) -> None:
    """Record metrics for successful context operations."""
    try:
        meter = metrics.get_meter(__name__)

        # Create basic labels
        labels = {"operation": operation_name, "operation_type": "manual"}

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
        logger.warning(f"Failed to record context success metrics: {e}")


def _record_context_error_metrics(
    extractor: AttributeExtractor,
    operation_name: str,
    duration: float,
    exception: Exception,
) -> None:
    """Record metrics for failed context operations."""
    try:
        meter = metrics.get_meter(__name__)

        # Create basic labels
        labels = {"operation": operation_name, "operation_type": "manual"}
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
        logger.warning(f"Failed to record context error metrics: {e}")
