# Structured Logging for Python

A comprehensive, production-ready structured logging solution that works with any Python application. This package provides a unified, framework-agnostic API for creating structured, JSON-formatted logs that are easy to parse, search, and analyze in modern observability platforms.

## Key Features

- **JSON Formatting**: Logs are automatically formatted as JSON, making them machine-readable and easy to process.
- **Event-based Logging**: Add event-context to logs and send only the filtered keys (defined) to Loki.
- **Contextual Logging**: Add contextual information to your logs in a thread-safe and async-safe manner.
- **Simple Configuration**: A single function to configure the entire logging system.
- **Framework-Agnostic**: Works with any Python application, from web frameworks to standalone scripts.

## Getting Started

### 1. Configuration

There are two ways to configure the logging system, depending on your needs.

#### Simple Configuration (Recommended for Logging Only)

For projects where you only need structured logging, the `setup_logging` function provides a quick and easy way to get started.

```python
from observability import LoggingConfig, setup_logging

log_config = LoggingConfig(
    service_name="my-cool-service",
    log_level="INFO",
    otlp_endpoint="http://172.31.0.1:4317",
    environment="production"
)
setup_logging(log_config)
```


### 2. Basic Usage

Once configured, you can get a logger instance and start logging messages. The logger's interface is similar to the standard Python `logging` module, but it accepts keyword arguments to add structured data to your logs.

```python
from observability import get_logger

logger = get_logger(__name__)

logger.info("User logged in successfully", user_id="12345", tenant_id="acme")
# Output (JSON):
# {
#   "timestamp": 1678886400.0,
#   "level": "INFO",
#   "message": "User logged in successfully",
#   "logger": "__main__",
#   "file": "my_app.py",
#   "line": 10,
#   "function": "main",
#   "service": "my-cool-service",
#   "environment": "production",
#   "user_id": "12345",
#   "tenant_id": "acme"
# }
```

### 3. Contextual Logging

You can add contextual information that will be included in all subsequent log messages within the same execution context (e.g., a request in a web application). This is particularly useful for adding request IDs or other contextual data.

```python
from observability.logging import add_log_context, get_logger

logger = get_logger(__name__)

def handle_request(request):
    add_log_context("request_id", request.id)
    logger.info("Processing request")
    # ... do some work ...
    logger.info("Request processed successfully")

# Both log messages will contain `request_id`.
```

### 4. Event-based Logging with Schemas

For more complex applications, you can define schemas for different event types to ensure consistency. This is useful for logging business events, workflow transitions, or other important events.

First, configure your event schemas at startup:

```python
from observability import WorkflowEventConfig, LoggingConfig, setup_logging

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
    format_json=True,
    workflow_event_config = workflow_cfg,
    environment="production"
)
setup_logging(log_config)

```

Then, use the `event_context` to log events that conform to the schema. The logger will automatically add the `event_type` and filter out any fields not defined in the extra_fields list or already defined in the WorkflowEventConfig.

```python
from observability import get_logger

# Get a logger with a specific event context
workflow_logger = get_logger(__name__, event_context="workflow")

workflow_logger.info(
    "Node executed", 
    node_name="process_input", 
    status="success"
    )

# Output (JSON):
# {
#   ...
#   "message": "Node executed",
#   "node_name": "process_input",
#   "status": "success"
# }
```

## Configuration (For Logging and Tracing)

If you plan to use both logging and tracing, you should use the `setup_observability` function with configuration objects. This gives you more control over the entire system.

```python
from observability import setup_observability, ObservabilityConfig

# Define the main observability configuration
obs_config = ObservabilityConfig(
    service_name="my-cool-service",
    environment="production",
    log_level="DEBUG",
)

# Initialize the system with the config object
setup_observability(obs_config)
```

This will also setup tracing and the logger can automatically include `trace_id` and `span_id` in your logs. This allows you to easily correlate logs with traces in your observability platform.