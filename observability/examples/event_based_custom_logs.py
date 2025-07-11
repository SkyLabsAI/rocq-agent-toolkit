from psi_verifier.observability import get_logger, ObservabilityConfig, setup_observability
from psi_verifier.observability.config import WorkflowEventConfig

# --- Observability Setup ---
workflow_cfg = WorkflowEventConfig(
    extra_fields=[
        "specification_goals",
        "structured_nl_spec",
        "max_user_attempts",
    ]
)
obs_config = ObservabilityConfig(
    service_name="event_based_custom_logs",
    workflow_event_config=workflow_cfg,
    log_level="INFO",
)
setup_observability(obs_config)

logger = get_logger(__name__, event_context="workflow")


logger.info("Hello, world!", spec="spec", node_name="start", node_count=1, transition_to="end", 
            specification_goals="to verify", structured_nl_spec="to spec", max_user_attempts=1)
