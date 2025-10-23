from __future__ import annotations
from dataclasses import dataclass, field
from typing import Optional, List
from ..logging.config import LoggingConfig


@dataclass
class ObservabilityConfig(LoggingConfig):
    """
    Unified configuration for observability features (Tracing and Logging).
    """

    # Feature toggles for tracing
    enable_tracing: bool = True
    enable_metrics: bool = False

    # LangSmith/LangChain integration features
    enable_langsmith: bool = True
    langchain_tracing_v2: bool = True
    langsmith_service_suffix: str = "langsmith"
    
    # Performance tuning
    batch_export_timeout_ms: int = 5000
    max_export_batch_size: int = 100
    metric_export_interval_ms: int = 10000
    
    # Global defaults for @trace decorator
    default_extractor: Optional[str] = None
    auto_metrics: bool = True
    trace_sampling_rate: float = 1.0
            
    @classmethod
    def from_environment(cls, **overrides: Any) -> "ObservabilityConfig":
        """
        Create configuration from environment variables.
        """
        env_config: dict[str, Any] = {
            'service_name': os.getenv('OTEL_SERVICE_NAME', 'unknown-service'),
            'service_version': os.getenv('OTEL_SERVICE_VERSION', 'unknown'),
            'service_namespace': os.getenv('OTEL_SERVICE_NAMESPACE', 'default'),
            'environment': os.getenv('OTEL_ENVIRONMENT'),
            'user_id': os.getenv('OTEL_USER_ID'),
            'session_id': os.getenv('OTEL_SESSION_ID'),
            'otlp_endpoint': os.getenv('OTEL_ENDPOINT', 'http://localhost:4317'),
            'log_level': os.getenv('OTEL_LOG_LEVEL', 'INFO'),
            'enable_tracing': os.getenv('OTEL_ENABLE_TRACING', 'true').lower() == 'true',
            'enable_metrics': os.getenv('OTEL_ENABLE_METRICS', 'true').lower() == 'true',
            'enable_logging': os.getenv('OTEL_ENABLE_LOGGING', 'true').lower() == 'true',
            'enable_otlp_log_export': os.getenv('OTEL_ENABLE_OTLP_LOG_EXPORT', 'true').lower() == 'true',
            'default_extractor': os.getenv('OTEL_DEFAULT_EXTRACTOR'),
            'trace_sampling_rate': float(os.getenv('OTEL_TRACE_SAMPLING_RATE', '1.0')),
            'enable_langsmith': os.getenv('OTEL_ENABLE_LANGSMITH', 'true').lower() == 'true',
            'langchain_tracing_v2': os.getenv('LANGCHAIN_TRACING_V2', 'true').lower() == 'true',
            'langsmith_service_suffix': os.getenv('OTEL_LANGSMITH_SERVICE_SUFFIX', 'langsmith'),
            'enable_async_logging': os.getenv('OTEL_ENABLE_ASYNC_LOGGING', 'false').lower() == 'true',
            'async_log_queue_size': int(os.getenv('OTEL_ASYNC_LOG_QUEUE_SIZE', '1000')),
            'async_log_queue_timeout': float(os.getenv('OTEL_ASYNC_LOG_QUEUE_TIMEOUT', '1.0')),
            'enable_auto_streaming': os.getenv('OTEL_ENABLE_AUTO_STREAMING', 'false').lower() == 'true',
            'auto_detect_chunk_fields': os.getenv('OTEL_AUTO_DETECT_CHUNK_FIELDS', 'true').lower() == 'true',
            'accumulated_content_field_name': os.getenv('OTEL_ACCUMULATED_CONTENT_FIELD_NAME', 'accumulated_content'),
            'enable_individual_chunk_logging': os.getenv('OTEL_ENABLE_INDIVIDUAL_CHUNK_LOGGING', 'false').lower() == 'true',
        }
        resource_attrs = {}
        for key, value in os.environ.items():
            if key.startswith('OTEL_RESOURCE_ATTR_'):
                attr_name = key[19:].lower()
                resource_attrs[attr_name] = value
        if resource_attrs:
            env_config['resource_attributes'] = resource_attrs
        env_config.update(overrides)
        return cls(**env_config)

    def validate(self) -> None:
        """
        Validate configuration values.
        """
        if not self.service_name or self.service_name == "unknown-service":
            raise ValueError("service_name must be provided and cannot be 'unknown-service'")
        if self.batch_export_timeout_ms <= 0:
            raise ValueError("batch_export_timeout_ms must be positive")
        if self.max_export_batch_size <= 0:
            raise ValueError("max_export_batch_size must be positive")
        if self.metric_export_interval_ms <= 0:
            raise ValueError("metric_export_interval_ms must be positive")
        if not 0.0 <= self.trace_sampling_rate <= 1.0:
            raise ValueError("trace_sampling_rate must be between 0.0 and 1.0")
        valid_log_levels = ['DEBUG', 'INFO', 'WARNING', 'ERROR', 'CRITICAL']
        if self.log_level.upper() not in valid_log_levels:
            raise ValueError(f"log_level must be one of {valid_log_levels}")
        if self.default_extractor:
            valid_extractors = ['http', 'rpc', 'database', 'workflow', 'langchain', 'custom']
            if self.default_extractor not in valid_extractors:
                raise ValueError(f"default_extractor must be one of {valid_extractors}")
        if not self.langsmith_service_suffix:
            raise ValueError("langsmith_service_suffix cannot be empty")
        if self.async_log_queue_size <= 0:
            raise ValueError("async_log_queue_size must be positive")
        if self.async_log_queue_timeout <= 0:
            raise ValueError("async_log_queue_timeout must be positive")



@dataclass
class ExtractorConfig:
    """Base configuration for extractors."""
    max_attribute_length: int = 1000
    include_sensitive_data: bool = False


@dataclass
class HttpExtractorConfig(ExtractorConfig):
    """Configuration for HTTP extractor."""
    include_headers: bool = False
    include_query_params: bool = True
    sensitive_headers: List[str] = field(default_factory=lambda: [
        'authorization', 'cookie', 'set-cookie', 'x-api-key', 'x-auth-token'
    ])


@dataclass
class RpcExtractorConfig(ExtractorConfig):
    """Configuration for RPC extractor."""
    system: str = "grpc"
    include_request_data: bool = False
    include_response_data: bool = False
    include_metadata: bool = True


@dataclass
class DatabaseExtractorConfig(ExtractorConfig):
    """Configuration for database extractor."""
    system: str = "sql"
    include_query: bool = False
    max_query_length: int = 1000


@dataclass
class WorkflowExtractorConfig(ExtractorConfig):
    """Configuration for workflow extractor."""
    include_state: bool = False
    include_input: bool = True
    include_output: bool = True


@dataclass
class LangChainExtractorConfig(ExtractorConfig):
    """Configuration for LangChain/LangGraph extractor."""
    include_inputs: bool = True
    include_outputs: bool = True
    include_token_usage: bool = True
    include_model_info: bool = True
    max_input_length: int = 1000
    max_output_length: int = 1000 
