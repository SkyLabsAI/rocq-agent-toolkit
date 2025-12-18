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
Output (JSON):
{
  "timestamp": 1678886400.0,
  "level": "INFO",
  "message": "User logged in successfully",
  "logger": "__main__",
  "file": "my_app.py",
  "line": 10,
  "function": "main",
  "service": "my-cool-service",
  "environment": "production",
  "user_id": "12345",
  "tenant_id": "acme"
}
```