
from dataclasses import is_dataclass
from observability.logging.config import (
    LoggingConfig,
    EventLogConfig,
    TrainingEventConfig,
    WorkflowEventConfig,
    EvaluationEventConfig,
    LangGraphEventConfig,
)

def test_logging_config_initialization():
    """Test initialization of LoggingConfig with default and custom values."""
    # Test with default values
    config = LoggingConfig(service_name="test-service")
    assert config.enable_logging is True
    assert config.enable_otlp_log_export is True
    assert config.log_level == "INFO"
    assert config.log_format_json is True
    assert config.training_event_config is None
    assert config.workflow_event_config is None
    assert config.evaluation_event_config is None
    assert config.langgraph_event_config is None

    # Test with custom values
    training_config = TrainingEventConfig(enabled=False)
    workflow_config = WorkflowEventConfig(enabled=False)
    evaluation_config = EvaluationEventConfig(enabled=False)
    langgraph_config = LangGraphEventConfig(enabled=False)
    
    config = LoggingConfig(
        service_name="test-service-custom",
        enable_logging=False,
        enable_otlp_log_export=False,
        log_level="DEBUG",
        log_format_json=False,
        training_event_config=training_config,
        workflow_event_config=workflow_config,
        evaluation_event_config=evaluation_config,
        langgraph_event_config=langgraph_config,
    )
    assert not config.enable_logging
    assert not config.enable_otlp_log_export
    assert config.log_level == "DEBUG"
    assert not config.log_format_json
    assert config.training_event_config is training_config
    assert config.workflow_event_config is workflow_config
    assert config.evaluation_event_config is evaluation_config
    assert config.langgraph_event_config is langgraph_config

def test_is_dataclass():
    """Test if all config classes are dataclasses."""
    assert is_dataclass(LoggingConfig)
    assert is_dataclass(EventLogConfig)
    assert is_dataclass(TrainingEventConfig)
    assert is_dataclass(WorkflowEventConfig)
    assert is_dataclass(EvaluationEventConfig)
    assert is_dataclass(LangGraphEventConfig)

def test_event_log_config_allowed_fields():
    """Test the allowed_fields method of EventLogConfig."""
    config = EventLogConfig(enabled=True, extra_fields=["custom1", "custom2"])
    
    # Manually set some 'include_' fields for testing, as EventLogConfig has none by default
    config.include_test1 = True
    config.include_test2 = False
    
    allowed = config.allowed_fields()
    
    # The method should pick up 'include_test1' and the extra fields
    assert "test1" in allowed
    assert "test2" not in allowed
    assert "custom1" in allowed
    assert "custom2" in allowed
    
    # Test for uniqueness
    config.extra_fields.append("test1")
    allowed = config.allowed_fields()
    assert allowed.count("test1") == 1

def test_training_event_config_fields():
    """Test TrainingEventConfig for default fields."""
    config = TrainingEventConfig()
    allowed = config.allowed_fields()
    expected = {"hyperparams", "dataset_info", "metrics", "reward_type", "reward_value"}
    assert set(allowed) == expected

def test_workflow_event_config_fields():
    """Test WorkflowEventConfig for default fields."""
    config = WorkflowEventConfig()
    allowed = config.allowed_fields()
    expected = {
        "cpp_code", "gallina_model", "rep_pred", "spec", "node_name",
        "raw_llm_response", "node_count", "transition_to", "status",
        "user_feedback", "command_execution_result", "model_version"
    }
    assert set(allowed) == expected

def test_evaluation_event_config_fields():
    """Test EvaluationEventConfig for default fields."""
    config = EvaluationEventConfig()
    allowed = config.allowed_fields()
    expected = {"dataset_info", "scores", "brick_server_result", "generation_kc"}
    # Note: 'sample_predictions' is False by default
    assert set(allowed) == expected

def test_langgraph_event_config_fields():
    """Test LangGraphEventConfig for default fields."""
    config = LangGraphEventConfig()
    allowed = config.allowed_fields()
    expected = {"node_name", "transition_to", "status", "error"}
    # Note: 'graph_state' is False by default
    assert set(allowed) == expected
    
def test_all_configs_initialization():
    """Test initialization of all event configs with custom values."""
    training_config = TrainingEventConfig(enabled=False, extra_fields=["extra1"], include_hyperparams=False)
    assert not training_config.enabled
    assert "extra1" in training_config.extra_fields
    assert "hyperparams" not in training_config.allowed_fields()

    workflow_config = WorkflowEventConfig(include_cpp_code=False)
    assert "cpp_code" not in workflow_config.allowed_fields()

    evaluation_config = EvaluationEventConfig(include_sample_predictions=True, max_sample_predictions=10)
    assert "sample_predictions" in evaluation_config.allowed_fields()
    assert evaluation_config.max_sample_predictions == 10

    langgraph_config = LangGraphEventConfig(include_graph_state=True)
    assert "graph_state" in langgraph_config.allowed_fields()
