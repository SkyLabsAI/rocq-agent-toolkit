import json
import logging
import threading
from unittest.mock import MagicMock, patch

import pytest
from observability.logging.core import (
    _event_schemas,
    _get_hostname,
    _loggers,
    add_log_context,
    clear_log_context,
    configure_event_schemas,
    get_global_event_context,
    get_log_context,
    get_logger,
    set_global_event_context,
    set_global_service_name,
    setup_logging,
)


# A mock handler to capture log records
class MockLogHandler(logging.Handler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.records = []

    def emit(self, record):
        self.records.append(record)

    def get_json_records(self):
        return [json.loads(record.getMessage()) for record in self.records]


@pytest.fixture(autouse=True)
def clean_global_state():
    """Fixture to clean up global logging state before and after each test."""
    # Setup: Clear global state before each test
    _loggers.clear()
    _event_schemas.clear()
    set_global_service_name(None)
    set_global_event_context(None)
    clear_log_context()

    yield  # This is where the test runs

    # Teardown: can be added here if needed, but setup covers it
    clear_log_context()


@pytest.fixture
def mock_handler():
    """Fixture to provide a mock log handler and attach it to the root logger."""
    handler = MockLogHandler()
    root_logger = logging.getLogger()
    original_level = root_logger.level

    root_logger.setLevel(logging.DEBUG)
    root_logger.addHandler(handler)

    yield handler

    # Teardown
    root_logger.removeHandler(handler)
    root_logger.setLevel(original_level)


def test_basic_logging(mock_handler):
    """Test basic logging methods."""
    logger = get_logger("test_logger", service_name="test_service")
    logger.info("This is a test", key="value")

    assert len(mock_handler.records) == 1
    log_json = mock_handler.get_json_records()[0]

    assert log_json["level"] == "INFO"
    assert log_json["message"] == "This is a test"
    assert log_json["service"] == "test_service"
    assert log_json["key"] == "value"
    assert "timestamp" in log_json
    assert "file" in log_json
    assert "line" in log_json


@patch("observability.logging.core.OTEL_AVAILABLE", True)
@patch("observability.logging.core.otel_trace")
def test_otel_correlation(mock_otel_trace, mock_handler):
    """Test OpenTelemetry trace correlation."""
    mock_span = MagicMock()
    mock_span_context = MagicMock()
    mock_span_context.is_valid = True
    mock_span_context.trace_id = 12345678901234567890123456789012
    mock_span_context.span_id = 1234567890123456
    mock_span.get_span_context.return_value = mock_span_context
    mock_span.is_recording.return_value = True
    mock_otel_trace.get_current_span.return_value = mock_span

    logger = get_logger("otel_logger")
    logger.info("Testing OTEL")

    log_json = mock_handler.get_json_records()[0]
    assert log_json["trace_id"] == f"{mock_span_context.trace_id:032x}"
    assert log_json["span_id"] == f"{mock_span_context.span_id:016x}"


@patch("observability.logging.core.OTEL_AVAILABLE", False)
def test_no_otel_correlation(mock_handler):
    """Test that no trace info is added when OTEL is unavailable."""
    logger = get_logger("no_otel_logger")
    logger.warning("No OTEL here")

    log_json = mock_handler.get_json_records()[0]
    assert "trace_id" not in log_json
    assert "span_id" not in log_json


def test_event_context_and_schema(mock_handler):
    """Test event context and schema filtering."""
    configure_event_schemas({"test_event": ["allowed_key", "another_key"]})
    logger = get_logger("event_logger", event_context="test_event")

    logger.info("Event test", allowed_key="yes", disallowed_key="no")

    log_json = mock_handler.get_json_records()[0]
    assert log_json["event_type"] == "test_event"
    assert "allowed_key" in log_json
    assert "disallowed_key" not in log_json


def test_log_context_management(mock_handler):
    """Test adding, getting, and clearing log context."""
    add_log_context("global_key", "global_value")

    logger = get_logger("context_logger")
    logger.error("Testing context")

    log_json = mock_handler.get_json_records()[0]
    assert log_json["global_key"] == "global_value"

    # Test context isolation in threads
    def thread_target():
        add_log_context("thread_key", "thread_value")
        logger.info("Thread log")

    thread = threading.Thread(target=thread_target)
    thread.start()
    thread.join()

    main_thread_context = get_log_context()
    assert "thread_key" not in main_thread_context

    # Check that the thread's log got the context
    thread_log_json = mock_handler.get_json_records()[1]
    assert thread_log_json["thread_key"] == "thread_value"

    clear_log_context()
    assert get_log_context() == {}


def test_global_settings(mock_handler):
    """Test global service name and event context."""
    set_global_service_name("global_service")
    set_global_event_context("global_event")
    configure_event_schemas({"global_event": ["only_this"]})

    logger = get_logger("global_settings_logger")
    logger.debug("Testing globals", only_this="is_allowed", not_this="is_not")

    log_json = mock_handler.get_json_records()[0]
    assert log_json["service"] == "global_service"
    assert log_json["event_type"] == "global_event"
    assert "only_this" in log_json
    assert "not_this" not in log_json

    assert get_global_event_context() == "global_event"


@patch("observability.logging.core.configure_logging")
@patch("observability.logging.core.add_log_context")
def test_setup_logging(mock_add_context, mock_configure):
    """Test the main setup_logging function."""
    setup_logging("setup_service", level="DEBUG", environment="test")

    mock_configure.assert_called_with("DEBUG", True)
    # It should be called for environment and hostname
    assert mock_add_context.call_count == 2
    mock_add_context.assert_any_call("environment", "test")
    mock_add_context.assert_any_call("hostname", _get_hostname())


def test_exception_logging(mock_handler):
    """Test logging with exc_info."""
    logger = get_logger("exception_logger")
    try:
        raise ValueError("Test exception")
    except ValueError:
        logger.exception("An error occurred")

    record = mock_handler.records[0]
    assert record.exc_info is not None
    log_json = json.loads(record.getMessage())
    assert log_json["message"] == "An error occurred"


def test_message_formatting(mock_handler):
    """Test message formatting with arguments."""
    logger = get_logger("format_logger")
    logger.info("User %s logged in from %s", "testuser", "127.0.0.1")

    log_json = mock_handler.get_json_records()[0]
    assert log_json["message"] == "User testuser logged in from 127.0.0.1"

    # Test failed formatting
    logger.error("Failed format: %s", "one", "two")
    log_json_fail = mock_handler.get_json_records()[1]
    assert log_json_fail["message"] == "Failed format: %s"
    assert "_format_error" in log_json_fail
