from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any


@dataclass
class LoggingConfig:
    """
    Configuration for logging features.
    """

    # Service identification
    service_name: str
    service_version: str = "unknown"
    service_namespace: str = "default"
    environment: str | None = None

    # User/Session identification (optional)
    user_id: str | None = None
    session_id: str | None = None

    # Resource attributes
    resource_attributes: dict[str, Any] = field(default_factory=dict)

    # OTLP Endpoint Configuration
    otlp_endpoint: str = "http://localhost:4317"
    otlp_insecure: bool = True

    # Custom headers for OTLP export
    custom_headers: dict[str, str] = field(default_factory=dict)

    # Logging configuration
    enable_logging: bool = True
    enable_otlp_log_export: bool = True
    enable_console_logging: bool = True
    log_level: str = "INFO"
    log_format_json: bool = True

    # Event-specific logging schemas (optional)
    training_event_config: TrainingEventConfig | None = None
    workflow_event_config: WorkflowEventConfig | None = None
    evaluation_event_config: EvaluationEventConfig | None = None
    langgraph_event_config: LangGraphEventConfig | None = None


@dataclass
class EventLogConfig:
    """Base configuration for event-specific structured logs."""

    enabled: bool = True
    extra_fields: list[str] = field(default_factory=list)

    def allowed_fields(self) -> list[str]:
        """Return the list of payload keys that are allowed for this event."""
        allowed: list[str] = []
        for attr_name, value in vars(self).items():
            if attr_name.startswith("include_") and value is True:
                allowed.append(attr_name[len("include_") :])
        allowed.extend(self.extra_fields)
        seen: set[str] = set()
        return [x for x in allowed if not (x in seen or seen.add(x))]


@dataclass
class TrainingEventConfig(EventLogConfig):
    include_hyperparams: bool = True
    include_dataset_info: bool = True
    include_metrics: bool = True
    include_reward_type: bool = True
    include_reward_value: bool = True


@dataclass
class WorkflowEventConfig(EventLogConfig):
    include_cpp_code: bool = True
    include_gallina_model: bool = True
    include_rep_pred: bool = True
    include_spec: bool = True
    include_node_name: bool = True
    include_raw_llm_response: bool = True
    include_node_count: bool = True
    include_transition_to: bool = True
    include_status: bool = True
    include_user_feedback: bool = True
    include_command_execution_result: bool = True
    include_model_version: bool = True


@dataclass
class EvaluationEventConfig(EventLogConfig):
    include_dataset_info: bool = True
    include_scores: bool = True
    include_brick_server_result: bool = True
    include_generation_kc: bool = True
    include_sample_predictions: bool = False
    max_sample_predictions: int = 5


@dataclass
class LangGraphEventConfig(EventLogConfig):
    include_graph_state: bool = False
    include_node_name: bool = True
    include_transition_to: bool = True
    include_status: bool = True
    include_error: bool = True
