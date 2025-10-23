from observability import LoggingConfig, setup_logging, get_logger, add_log_context, WorkflowEventConfig
from collections import namedtuple
workflow_cfg = WorkflowEventConfig(
    extra_fields=[
        "specification_goals",
        "structured_nl_spec",
        "max_user_attempts",
    ]
)
log_config = LoggingConfig(
    service_name="my-cool-service",
    log_level="INFO",
    otlp_endpoint="http://172.31.0.1:4317",
    environment="production",
    workflow_event_config=workflow_cfg,
)
setup_logging(log_config)

logger = get_logger(__name__)

logger.info("User logged in successfully", user_id="12345", tenant_id="acme")


def handle_request(request):
    add_log_context("request_id", request["id"])
    logger.info("Processing request")
    # ... do some work ...
    logger.info("Request processed successfully")


Request = {"id": "12345"}
handle_request(request=Request)

workflow_logger = get_logger(__name__, event_context="workflow")

workflow_logger.info(
    "Node executed",
    node_name="process_input",
    status="success",
    specification_goals="12345",
    structured_nl_spec="test",
    key_not_defined="value"
    )
