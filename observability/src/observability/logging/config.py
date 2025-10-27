from __future__ import annotations

from dataclasses import dataclass, field
from typing import List, Optional

from ..config import CoreConfig


@dataclass
class LoggingConfig(CoreConfig):
    """
    Configuration for logging features.
    """

    # Logging configuration
    enable_logging: bool = True
    enable_otlp_log_export: bool = True
    log_level: str = "INFO"
    log_format_json: bool = True

    # Event-specific logging schemas (optional)
    training_event_config: Optional["TrainingEventConfig"] = None
    workflow_event_config: Optional["WorkflowEventConfig"] = None
    evaluation_event_config: Optional["EvaluationEventConfig"] = None
    langgraph_event_config: Optional["LangGraphEventConfig"] = None


@dataclass
class EventLogConfig:
    """Base configuration for event-specific structured logs."""

    enabled: bool = True
    extra_fields: List[str] = field(default_factory=list)

    def allowed_fields(self) -> List[str]:
        """Return the list of payload keys that are allowed for this event."""
        allowed: List[str] = []
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
