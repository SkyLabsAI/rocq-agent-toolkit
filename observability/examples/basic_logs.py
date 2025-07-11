from psi_verifier.observability import get_logger, ObservabilityConfig, setup_observability
obs_config = ObservabilityConfig(
    service_name="basic_logs",
    log_level="INFO",
)
setup_observability(obs_config)
logger = get_logger(__name__)

logger.info("Hello, world!")
