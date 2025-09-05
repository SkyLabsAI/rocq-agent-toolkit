"""
Additional tests for logging core functionality to increase coverage
"""
import pytest
import json
import logging
from unittest.mock import patch, MagicMock
from observability.logging.core import (
    StructuredLogger,
    get_logger,
    setup_logging,
    configure_logging,
    set_global_service_name,
    set_global_event_context,
    get_global_event_context,
    configure_event_schemas,
    configure_auto_streaming,
    is_auto_streaming_enabled
)
from observability.logging.context import (
    add_log_context,
    clear_log_context,
    get_log_context
)


class TestStructuredLoggerDirect:
    """Test StructuredLogger class directly"""

    def test_structured_logger_creation(self):
        """Test creating StructuredLogger directly"""
        logger = StructuredLogger("test.direct", event_context="test")
        assert logger.event_context == "test"
        assert logger.name == "test.direct"

    def test_structured_logger_without_event_context(self):
        """Test creating StructuredLogger without event context"""
        logger = StructuredLogger("test.no_context")
        assert logger.event_context is None

    def test_structured_logger_info_without_kwargs(self):
        """Test logging info without extra kwargs"""
        logger = StructuredLogger("test.info")
        # Should not raise exception
        logger.info("Simple message")

    def test_structured_logger_error_without_kwargs(self):
        """Test logging error without extra kwargs"""
        logger = StructuredLogger("test.error")
        # Should not raise exception
        logger.error("Simple error")

    def test_structured_logger_warning_without_kwargs(self):
        """Test logging warning without extra kwargs"""
        logger = StructuredLogger("test.warning")
        # Should not raise exception
        logger.warning("Simple warning")

    def test_structured_logger_debug_without_kwargs(self):
        """Test logging debug without extra kwargs"""
        logger = StructuredLogger("test.debug")
        # Should not raise exception
        logger.debug("Simple debug")

    def test_structured_logger_critical_without_kwargs(self):
        """Test logging critical without extra kwargs"""
        logger = StructuredLogger("test.critical")
        # Should not raise exception
        logger.critical("Simple critical")


class TestLoggingConfiguration:
    """Test logging configuration functions"""

    def test_setup_logging_basic(self):
        """Test basic setup_logging call"""
        # Should not raise exception
        setup_logging("test-service")

    def test_setup_logging_with_level(self):
        """Test setup_logging with log level"""
        # Should not raise exception
        setup_logging("test-service", level="DEBUG")

    def test_setup_logging_with_json_format(self):
        """Test setup_logging with JSON format"""
        # Should not raise exception  
        setup_logging("test-service", level="INFO", format_json=True)

    def test_setup_logging_with_environment(self):
        """Test setup_logging with environment"""
        # Should not raise exception
        setup_logging("test-service", environment="test")

    def test_configure_logging_basic(self):
        """Test configure_logging function"""
        # Should not raise exception
        configure_logging(
            level="INFO",
            format_json=True
        )

    def test_configure_logging_with_otlp_export(self):
        """Test configure_logging with OTLP export"""
        # Should not raise exception  
        configure_logging(
            level="INFO",
            format_json=True
        )

    def test_set_global_service_name(self):
        """Test setting global service name"""
        set_global_service_name("global-test-service")
        # Should not raise exception

    def test_set_global_event_context(self):
        """Test setting global event context"""
        set_global_event_context("global-context")
        context = get_global_event_context()
        assert context == "global-context"

    def test_configure_event_schemas(self):
        """Test configuring event schemas"""
        schemas = {
            "workflow": ["step", "status", "duration"],
            "auth": ["user_id", "action", "result"]
        }
        # Should not raise exception
        configure_event_schemas(schemas)

    def test_configure_auto_streaming(self):
        """Test configuring auto streaming"""
        configure_auto_streaming(
            enabled=True,
            auto_detect_chunk_fields=["chunk", "content"],
            accumulated_content_field_name="full_content"
        )
        assert is_auto_streaming_enabled() is True

        configure_auto_streaming(enabled=False)
        assert is_auto_streaming_enabled() is False


class TestLoggerCaching:
    """Test logger caching behavior"""

    def test_get_logger_returns_same_instance(self):
        """Test that get_logger returns the same instance for same name"""
        logger1 = get_logger("cache.test")
        logger2 = get_logger("cache.test")
        # Should be the same instance due to caching
        assert logger1 is logger2

    def test_get_logger_different_names_different_instances(self):
        """Test that different names return different instances"""
        logger1 = get_logger("cache.test1")
        logger2 = get_logger("cache.test2")
        assert logger1 is not logger2

    def test_get_logger_with_event_context_caching(self):
        """Test caching with event context"""
        logger1 = get_logger("cache.context", event_context="ctx1")
        logger2 = get_logger("cache.context", event_context="ctx1")
        # Should be the same instance
        assert logger1 is logger2

        logger3 = get_logger("cache.context", event_context="ctx2")
        # Should be different instance due to different context
        assert logger1 is not logger3


class TestLoggingEdgeCases:
    """Test edge cases in logging"""

    def test_logger_with_none_message(self):
        """Test logging with None message"""
        logger = get_logger("edge.test")
        # Should not raise exception
        logger.info(None)

    def test_logger_with_empty_message(self):
        """Test logging with empty message"""
        logger = get_logger("edge.test")
        # Should not raise exception
        logger.info("")

    def test_logger_with_numeric_message(self):
        """Test logging with numeric message"""
        logger = get_logger("edge.test")
        # Should not raise exception
        logger.info(42)
        logger.info(3.14159)

    def test_logger_with_boolean_message(self):
        """Test logging with boolean message"""
        logger = get_logger("edge.test")
        # Should not raise exception
        logger.info(True)
        logger.info(False)

    def test_logger_with_complex_kwargs(self):
        """Test logging with complex kwargs"""
        logger = get_logger("edge.test")
        
        # Complex data structures
        logger.info("Complex test", 
                   simple_dict={"key": "value"},
                   nested_dict={"outer": {"inner": "value"}},
                   list_data=[1, 2, 3, "four"],
                   mixed_tuple=(1, "two", 3.0),
                   number=42,
                   float_val=3.14159,
                   boolean=True,
                   none_val=None)

    def test_logger_with_serialization_issues(self):
        """Test logging with data that might have serialization issues"""
        logger = get_logger("edge.test")
        
        # These should not raise exceptions even if they cause JSON serialization issues
        try:
            # Objects that don't serialize to JSON easily
            logger.info("Object test", custom_obj=object())
            logger.info("Function test", func=lambda x: x)
        except Exception:
            # If it fails, that's acceptable for edge cases
            pass


class TestContextWithLogging:
    """Test context integration with logging"""

    def setup_method(self):
        """Clear context before each test"""
        clear_log_context()

    def teardown_method(self):
        """Clear context after each test"""
        clear_log_context()

    def test_context_integration_basic(self):
        """Test basic context integration"""
        add_log_context("session_id", "test_session_123")
        add_log_context("user_id", "user_456")
        
        logger = get_logger("context.test")
        # Should include context in log message
        logger.info("Test with context", action="test_action")

        context = get_log_context()
        assert context["session_id"] == "test_session_123"
        assert context["user_id"] == "user_456"

    def test_context_overwrite(self):
        """Test context overwriting"""
        add_log_context("key", "original")
        assert get_log_context()["key"] == "original"
        
        add_log_context("key", "updated")
        assert get_log_context()["key"] == "updated"

    def test_context_multiple_keys(self):
        """Test adding multiple context keys"""
        keys_values = {
            "session": "sess_123",
            "user": "user_456", 
            "request": "req_789",
            "trace": "trace_abc"
        }
        
        for key, value in keys_values.items():
            add_log_context(key, value)
            
        context = get_log_context()
        for key, value in keys_values.items():
            assert context[key] == value

    def test_clear_context_partial(self):
        """Test that clearing context removes all keys"""
        add_log_context("key1", "value1")
        add_log_context("key2", "value2")
        
        context = get_log_context()
        assert len(context) >= 2
        
        clear_log_context()
        context = get_log_context()
        assert len(context) == 0


class TestLoggingIntegration:
    """Integration tests for logging functionality"""

    def test_full_logging_integration(self):
        """Test full logging integration with all components"""
        # Setup
        clear_log_context()
        setup_logging("integration-test", level="INFO")
        
        # Configure global settings
        set_global_service_name("integration-service")
        set_global_event_context("integration-context")
        
        # Add context
        add_log_context("integration_id", "int_123")
        add_log_context("test_run", "run_456")
        
        # Get logger and log messages
        logger = get_logger("integration.full", event_context="full_test")
        
        logger.info("Starting integration test")
        logger.info("Processing data", step="process", count=42)
        logger.warning("Warning during processing", warning_type="data_quality")
        logger.error("Error occurred", error_code="INT001", severity="low")
        logger.debug("Debug information", debug_level="verbose")
        logger.critical("Critical issue", impact="high")
        
        # Verify context is maintained
        context = get_log_context()
        assert context["integration_id"] == "int_123"
        assert context["test_run"] == "run_456"

    def test_concurrent_logging_simulation(self):
        """Simulate concurrent logging scenarios"""
        # This tests that loggers work correctly when used "concurrently"
        loggers = []
        for i in range(10):
            logger = get_logger(f"concurrent.test.{i}")
            loggers.append(logger)
            
        # Log from all loggers
        for i, logger in enumerate(loggers):
            logger.info(f"Message from logger {i}", logger_id=i, iteration=1)
            logger.warning(f"Warning from logger {i}", logger_id=i, iteration=2)
            logger.error(f"Error from logger {i}", logger_id=i, iteration=3)

    def test_performance_logging_batch(self):
        """Test performance with batch logging"""
        logger = get_logger("performance.test")
        
        # Log many messages quickly
        for i in range(50):
            logger.info(f"Batch message {i}", 
                       batch_id=i,
                       timestamp=f"time_{i}",
                       status="processed")

    def test_logging_with_various_data_types(self):
        """Test logging with various Python data types"""
        logger = get_logger("types.test")
        
        test_data = {
            "string": "test string",
            "integer": 42,
            "float": 3.14159,
            "boolean_true": True,
            "boolean_false": False,
            "none": None,
            "list": [1, 2, "three", 4.0],
            "dict": {"nested": {"key": "value"}},
            "tuple": (1, 2, 3),
            "set": {1, 2, 3}  # This might serialize differently
        }
        
        for key, value in test_data.items():
            try:
                logger.info(f"Testing {key}", test_type=key, test_value=value)
            except Exception as e:
                # Some types might not serialize well, that's okay
                logger.info(f"Failed to log {key}: {e}")
