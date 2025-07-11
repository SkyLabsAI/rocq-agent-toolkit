from psi_verifier.observability import get_logger, ObservabilityConfig, setup_observability


obs_config = ObservabilityConfig(
    service_name="event_based_logs",
    log_level="INFO",
)
setup_observability(obs_config)

logger = get_logger(__name__, event_context="workflow")
logger.info("Hello, world!", spec="spec", node_name="start", node_count=1, transition_to="end")