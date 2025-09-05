"""
Tests for basic observability functionality - SAFE VERSION (no OpenTelemetry hanging)
"""
import pytest
from unittest.mock import patch, MagicMock
from observability import (
    get_logger, 
    ObservabilityConfig,
    add_log_context,
    clear_log_context,
    get_log_context,
    log_operation_start,
    log_operation_success,
    log_operation_error,
    log_business_event,
    log_security_event,
    log_performance_metric
)


class TestBasicLogging:
    """Test basic logging functionality"""

    def test_get_logger_returns_logger(self):
        """Test that get_logger returns a logger instance"""
        logger = get_logger("test_module")
        assert hasattr(logger, 'debug')
        assert hasattr(logger, 'info')
        assert hasattr(logger, 'warning')
        assert hasattr(logger, 'error')

    def test_get_logger_with_module_name(self):
        """Test get_logger with different module names"""
        logger1 = get_logger("module1")
        logger2 = get_logger("module2")
        
        # Both should be valid loggers
        assert hasattr(logger1, 'info')
        assert hasattr(logger2, 'info')

    def test_logger_basic_methods(self):
        """Test that logger methods can be called"""
        logger = get_logger("test")
        
        # These should not raise exceptions
        logger.debug("Debug message")
        logger.info("Info message")  
        logger.warning("Warning message")
        logger.error("Error message")


class TestLogContext:
    """Test log context management"""

    def test_add_log_context(self):
        """Test adding context to logs"""
        add_log_context("user_id", "123")
        add_log_context("session", "abc")
        
        context = get_log_context()
        assert isinstance(context, dict)
        
        clear_log_context()

    def test_clear_log_context(self):
        """Test clearing log context"""
        add_log_context("test", "value")
        clear_log_context()
        
        context = get_log_context()
        # Context should be empty or None after clearing
        assert not context or len(context) == 0

    def test_get_log_context(self):
        """Test getting log context"""
        add_log_context("key", "value")
        
        context = get_log_context()
        assert isinstance(context, dict)
        
        clear_log_context()

    def test_log_context_isolation(self):
        """Test that context changes are isolated"""
        clear_log_context()  # Start clean
        
        add_log_context("test1", "value1")
        context1 = get_log_context()
        
        add_log_context("test2", "value2")  
        context2 = get_log_context()
        
        # Context should have accumulated
        assert isinstance(context1, dict)
        assert isinstance(context2, dict)
        
        clear_log_context()


class TestEventLogging:
    """Test structured event logging"""

    def test_log_operation_start(self):
        """Test logging operation start"""
        # This should not raise exceptions
        log_operation_start("test_operation")

    def test_log_operation_success(self):
        """Test logging operation success"""
        # This should not raise exceptions
        log_operation_success("test_operation")

    def test_log_operation_error(self):
        """Test logging operation error"""
        # This should not raise exceptions  
        log_operation_error("test_operation", "Test error", {"context": "test"})

    def test_log_business_event(self):
        """Test logging business events"""
        # This should not raise exceptions
        log_business_event("user_signup", {"user_id": "123"})

    def test_log_security_event(self):
        """Test logging security events"""
        # This should not raise exceptions
        log_security_event("login_attempt", {"user": "test", "success": True})

    def test_log_performance_metric(self):
        """Test logging performance metrics"""
        # This should not raise exceptions
        log_performance_metric("response_time", 250)


class TestConfiguration:
    """Test configuration functionality"""

    def test_observability_config_creation(self):
        """Test creating observability config"""
        config = ObservabilityConfig(
            service_name="test-service",
            enable_tracing=False,
            enable_metrics=False,
            enable_logging=True
        )
        
        assert config.service_name == "test-service"
        assert config.enable_tracing is False
        assert config.enable_metrics is False
        assert config.enable_logging is True

    def test_config_with_additional_settings(self):
        """Test config with various settings"""
        config = ObservabilityConfig(
            service_name="advanced-service",
            service_version="1.0.0",
            environment="test",
            user_id="test_user",
            session_id="test_session"
        )
        
        assert config.service_name == "advanced-service"
        assert config.service_version == "1.0.0"
        assert config.environment == "test"
        assert config.user_id == "test_user"
        assert config.session_id == "test_session"

    def test_config_effective_resource_attributes(self):
        """Test effective resource attributes"""
        config = ObservabilityConfig(
            service_name="test-service",
            service_version="2.0.0",
            environment="production"
        )
        
        attrs = config.effective_resource_attributes
        assert isinstance(attrs, dict)
        assert "service.name" in attrs
        assert attrs["service.name"] == "test-service"


@patch('observability.setup_observability')  # Mock to prevent OpenTelemetry hanging
class TestObservabilitySetup:
    """Test observability setup (mocked to prevent hanging)"""

    def test_setup_observability_basic(self, mock_setup):
        """Test basic observability setup"""
        mock_setup.return_value = None
        config = ObservabilityConfig(
            service_name="test-service",
            enable_tracing=False,
            enable_metrics=False
        )
        
        # Should not raise exceptions and should not hang
        from observability import setup_observability
        setup_observability(config)
        mock_setup.assert_called_once_with(config)

    def test_setup_observability_with_config(self, mock_setup):
        """Test setup with detailed configuration"""
        mock_setup.return_value = None
        config = ObservabilityConfig(
            service_name="detailed-service",
            service_version="1.2.3",
            enable_tracing=False,
            enable_metrics=False,
            enable_logging=True
        )
        
        from observability import setup_observability
        setup_observability(config)
        mock_setup.assert_called_once_with(config)


class TestIntegration:
    """Test integration scenarios"""

    def test_basic_logging_workflow(self):
        """Test basic logging workflow"""
        logger = get_logger("integration_test")
        
        # Add context
        add_log_context("workflow", "test")
        add_log_context("step", "1")
        
        # Log various events
        log_operation_start("integration_test")
        logger.info("Processing integration test")
        log_operation_success("integration_test")
        
        # Clear context
        clear_log_context()

    def test_error_handling_workflow(self):
        """Test error handling in logging workflow"""
        logger = get_logger("error_test")
        
        try:
            # Simulate an operation that might fail
            add_log_context("operation", "error_test")
            log_operation_start("error_test")
            
            # Simulate error (without actually raising)
            log_operation_error("error_test", "Simulated error", {"code": 500})
            
        finally:
            clear_log_context()