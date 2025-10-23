from unittest.mock import patch, MagicMock
import logging
import pytest

from observability.logging.config import (
    LoggingConfig,
    TrainingEventConfig,
    WorkflowEventConfig
)
from observability.logging.setup import setup_logging, FixedLoggingHandler

@patch('observability.logging.setup.core_setup_logging')
@patch('observability.logging.setup.configure_event_schemas')
@patch('observability.logging.setup._setup_otlp_log_export')
def test_setup_logging_all_enabled(mock_setup_otlp, mock_configure_schemas, mock_core_setup):
    """
    Test setup_logging with OTLP and event schemas enabled.
    """
    config = LoggingConfig(
        service_name="test-service",
        log_level="DEBUG",
        log_format_json=True,
        environment="test",
        enable_otlp_log_export=True,
        training_event_config=TrainingEventConfig(enabled=True),
        workflow_event_config=WorkflowEventConfig(enabled=True, include_cpp_code=False)
    )

    setup_logging(config)

    # 1. Verify that core logging setup is called correctly
    mock_core_setup.assert_called_once_with(
        service_name="test-service",
        level="DEBUG",
        format_json=True,
        environment="test"
    )

    # 2. Verify that event schemas are configured
    assert mock_configure_schemas.called
    schema_dict = mock_configure_schemas.call_args[0][0]
    assert "training" in schema_dict
    assert "workflow" in schema_dict
    assert "hyperparams" in schema_dict["training"]
    assert "cpp_code" not in schema_dict["workflow"]

    # 3. Verify that OTLP export is set up
    mock_setup_otlp.assert_called_once_with(config)

@patch('observability.logging.setup.core_setup_logging')
@patch('observability.logging.setup.configure_event_schemas')
@patch('observability.logging.setup._setup_otlp_log_export')
def test_setup_logging_otlp_disabled(mock_setup_otlp, mock_configure_schemas, mock_core_setup):
    """
    Test setup_logging with OTLP export disabled.
    """
    config = LoggingConfig(
        service_name="test-service-no-otlp",
        enable_otlp_log_export=False,
        training_event_config=TrainingEventConfig(enabled=False)  # Schema disabled
    )

    setup_logging(config)

    # Core setup should still be called
    mock_core_setup.assert_called_once()
    
    # Schemas should not be configured if no event configs are enabled
    assert not mock_configure_schemas.called

    # OTLP setup should NOT be called
    assert not mock_setup_otlp.called

@patch('opentelemetry.sdk._logs.LoggingHandler.emit')
@patch('inspect.stack')
def test_fixed_logging_handler_emit(mock_inspect_stack, mock_parent_emit):
    """
    Test that FixedLoggingHandler correctly identifies the caller frame.
    """
    # Create a mock stack that simulates a call from user code through logging infrastructure
    mock_frame_user = MagicMock()
    mock_frame_user.filename = "/path/to/user_app/main.py"
    mock_frame_user.function = "user_function"
    mock_frame_user.lineno = 42

    mock_frame_logger_log = MagicMock()
    mock_frame_logger_log.filename = "/path/to/lib/logging/core.py"
    mock_frame_logger_log.function = "_log"
    mock_frame_logger_log.lineno = 100

    mock_frame_handler_emit = MagicMock()
    mock_frame_handler_emit.filename = "/path/to/lib/opentelemetry/sdk/_logs/__init__.py"
    mock_frame_handler_emit.function = "emit"
    mock_frame_handler_emit.lineno = 200

    # The stack is returned from innermost to outermost call
    mock_inspect_stack.return_value = [
        mock_frame_handler_emit,
        mock_frame_logger_log,
        mock_frame_user,
        # ... other frames below
    ]

    handler = FixedLoggingHandler()
    mock_record = logging.LogRecord(
        name='test', level=logging.INFO, pathname='', lineno=0,
        msg='test message', args=(), exc_info=None
    )

    # Call the emit method
    handler.emit(mock_record)

    # Assert that the record was updated with info from the user frame
    assert mock_record.pathname == "/path/to/user_app/main.py"
    assert mock_record.filename == "main.py"
    assert mock_record.funcName == "user_function"
    assert mock_record.lineno == 42
    assert mock_record.module == "main"

    # Assert that the parent's emit was called with the modified record
    mock_parent_emit.assert_called_once_with(mock_record)
