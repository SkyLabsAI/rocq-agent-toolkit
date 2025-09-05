"""
Observability Configuration

This module provides configuration management for the observability package.
It supports both environment-based and programmatic configuration with the
new framework-agnostic approach.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import Dict, Optional, Any, List
import os


@dataclass
class ObservabilityConfig:
    """
    Configuration for observability features.
    
    This class centralizes all configuration options and provides sensible defaults.
    Settings can be loaded from environment variables or set programmatically.
    """
    
    # Service identification
    service_name: str
    service_version: str = "unknown"
    service_namespace: str = "default"
    environment: Optional[str] = None  # Add environment field
    
    # User/Session identification (optional)
    include_run_id: bool = False
    user_id: Optional[str] = None
    session_id: Optional[str] = None
    
    # OpenTelemetry endpoints
    otlp_endpoint: str = "http://localhost:4317"
    otlp_insecure: bool = True
    
    # Feature toggles
    enable_tracing: bool = True
    enable_metrics: bool = False
    enable_logging: bool = True
    enable_otlp_log_export: bool = True  # New flag to control OTLP log export specifically
    
    # LangSmith/LangChain integration
    enable_langsmith: bool = True
    langchain_tracing_v2: bool = True  # Added for V2 tracing
    langsmith_service_suffix: str = "langsmith"
    
    # Performance tuning
    batch_export_timeout_ms: int = 5000
    max_export_batch_size: int = 100
    metric_export_interval_ms: int = 10000
    
    # Logging configuration
    log_level: str = "INFO"
    log_format_json: bool = True
    
    # Asynchronous logging configuration
    enable_async_logging: bool = False
    async_log_queue_size: int = 1000
    async_log_queue_timeout: float = 1.0
    
    # Auto-streaming configuration
    enable_auto_streaming: bool = False
    
    # Generic streaming behavior
    auto_detect_chunk_fields: bool = True  # Automatically detect any field as chunk content
    accumulated_content_field_name: str = "accumulated_content"  # Output field name for final content
    enable_individual_chunk_logging: bool = False  # Flag to enable/disable individual chunk logs
    
    # Reserved field names (these won't be treated as chunk content)
    streaming_reserved_fields: List[str] = field(default_factory=lambda: [
        "streaming_session_id", "streaming_mode", "streaming_complete", "stream_end",
        "user_input", "model", "chunk_number", "chunk_length", "timestamp",
        "level", "message", "logger", "service", "environment", "hostname",
        "run_id", "event_type", "exc_info", "total_chunks", "duration_ms",
        "accumulated_length"
    ])
    
    # Backward compatibility - specific field name mappings (optional)
    streaming_field_names: Dict[str, str] = field(default_factory=lambda: {
        "user_input": "user_input",
        "model": "model",
        "streaming_mode": "streaming_mode",
        "streaming_session_id": "streaming_session_id",
        "total_chunks": "total_chunks"
    })
    
    # Global defaults for @trace decorator
    default_extractor: Optional[str] = None
    auto_metrics: bool = True
    trace_sampling_rate: float = 1.0  # Sample 100% by default
    
    # Resource attributes (added to all traces/metrics)
    resource_attributes: Dict[str, Any] = field(default_factory=dict)
    
    # Custom headers for OTLP export
    custom_headers: Dict[str, str] = field(default_factory=dict)
    
    # ---------------------------------------------------------------------
    # Event-specific logging schemas (optional)
    # ---------------------------------------------------------------------

    training_event_config: Optional['TrainingEventConfig'] = None
    workflow_event_config: Optional['WorkflowEventConfig'] = None
    evaluation_event_config: Optional['EvaluationEventConfig'] = None
    langgraph_event_config: Optional['LangGraphEventConfig'] = None
    streaming_event_config: Optional['StreamingEventConfig'] = None

    def __post_init__(self) -> None:
        """
        Sets environment variables for LangSmith integration based on config.

        This ensures that when LangSmith is enabled, it correctly routes its
        traces through the standard OpenTelemetry pipeline, rather than its
        own cloud endpoint. This is crucial for unified tracing.
        """
        if self.enable_langsmith:
            # LangChain V2 tracing is controlled by this config.
            os.environ["LANGCHAIN_TRACING_V2"] = "true" if self.langchain_tracing_v2 else "false"
            
            # When using LangSmith with a local OTLP endpoint, clear the
            # cloud-specific endpoints and API keys.
            os.environ["LANGCHAIN_ENDPOINT"] = ""
            os.environ["LANGCHAIN_API_KEY"] = ""
            os.environ["LANGSMITH_API_URL"] = ""
            os.environ["LANGSMITH_API_KEY"] = ""

            # Force LangSmith to use the OTLP exporter and point it to our
            # configured OTLP endpoint (e.g., a local Tempo/Alloy instance).
            os.environ["LANGSMITH_OTEL_ENABLED"] = "true"
            os.environ["LANGSMITH_OTEL_ENDPOINT"] = self.otlp_endpoint
        else:
            # If LangSmith integration is disabled, ensure tracing is turned off.
            os.environ["LANGCHAIN_TRACING_V2"] = "false"
    
    @classmethod
    def from_environment(cls, **overrides: Any) -> "ObservabilityConfig":
        """
        Create configuration from environment variables.
        
        Environment variables:
        - OTEL_ENDPOINT → otlp_endpoint
        - OTEL_SERVICE_NAME → service_name  
        - OTEL_SERVICE_VERSION → service_version
        - OTEL_SERVICE_NAMESPACE → service_namespace
        - OTEL_ENVIRONMENT → environment
        - OTEL_USER_ID → user_id
        - OTEL_SESSION_ID → session_id
        - OTEL_LOG_LEVEL → log_level
        - OTEL_ENABLE_TRACING → enable_tracing
        - OTEL_ENABLE_METRICS → enable_metrics
        - OTEL_ENABLE_LOGGING → enable_logging
        - OTEL_ENABLE_OTLP_LOG_EXPORT → enable_otlp_log_export
        - OTEL_TRACE_SAMPLING_RATE → trace_sampling_rate
        - OTEL_DEFAULT_EXTRACTOR → default_extractor
        - OTEL_ENABLE_LANGSMITH → enable_langsmith
        - LANGCHAIN_TRACING_V2 → langchain_tracing_v2
        - LANGCHAIN_TRACING_V2 → langchain_tracing_v2
        - OTEL_LANGSMITH_SERVICE_SUFFIX → langsmith_service_suffix
        - OTEL_ENABLE_ASYNC_LOGGING → enable_async_logging
        - OTEL_ASYNC_LOG_QUEUE_SIZE → async_log_queue_size
        - OTEL_ASYNC_LOG_QUEUE_TIMEOUT → async_log_queue_timeout
        - OTEL_ENABLE_AUTO_STREAMING → enable_auto_streaming
        - OTEL_AUTO_DETECT_CHUNK_FIELDS → auto_detect_chunk_fields
        - OTEL_ACCUMULATED_CONTENT_FIELD_NAME → accumulated_content_field_name
        - OTEL_ENABLE_INDIVIDUAL_CHUNK_LOGGING → enable_individual_chunk_logging
        
        Args:
            **overrides: Values to override environment/defaults
            
        Returns:
            ObservabilityConfig instance
            
        Example:
            # Load from environment with overrides
            config = ObservabilityConfig.from_environment(
                service_name="my-service",
                log_level="DEBUG"
            )
        """
        env_config: Dict[str, Any] = {
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
        
        # Parse resource attributes from environment
        resource_attrs = {}
        for key, value in os.environ.items():
            if key.startswith('OTEL_RESOURCE_ATTR_'):
                attr_name = key[19:].lower()  # Remove OTEL_RESOURCE_ATTR_ prefix
                resource_attrs[attr_name] = value
        
        if resource_attrs:
            env_config['resource_attributes'] = resource_attrs
        
        # Apply overrides
        env_config.update(overrides)
        
        return cls(**env_config)
    
    def validate(self) -> None:
        """
        Validate configuration values.
        
        Raises:
            ValueError: If configuration is invalid
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
        
        # Validate default extractor if provided
        if self.default_extractor:
            valid_extractors = ['http', 'rpc', 'database', 'workflow', 'langchain', 'custom']
            if self.default_extractor not in valid_extractors:
                raise ValueError(f"default_extractor must be one of {valid_extractors}")
        
        # Validate LangSmith service suffix
        if not self.langsmith_service_suffix:
            raise ValueError("langsmith_service_suffix cannot be empty")
        
        # Validate async logging configuration
        if self.async_log_queue_size <= 0:
            raise ValueError("async_log_queue_size must be positive")
        
        if self.async_log_queue_timeout <= 0:
            raise ValueError("async_log_queue_timeout must be positive")
    
    @property
    def effective_resource_attributes(self) -> Dict[str, str]:
        """Get complete resource attributes including service info."""
        attrs = {
            "service.name": self.service_name,
            "service.version": self.service_version,
            "service.namespace": self.service_namespace,
        }
        
        # Add environment if specified
        if self.environment:
            attrs["deployment.environment"] = self.environment
            
        attrs.update(self.resource_attributes)
        return attrs


# Configuration classes for specific extractors
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


# ---------------------------------------------------------------------------
# Event-specific structured-logging configuration
# ---------------------------------------------------------------------------


@dataclass
class EventLogConfig:
    """Base configuration for event-specific structured logs."""

    enabled: bool = True
    # Additional field names (without the ``include_`` prefix) that should be
    # passed through even if no dedicated *include_* flag exists.
    extra_fields: List[str] = field(default_factory=list)

    def allowed_fields(self) -> List[str]:
        """Return the list of payload keys that are allowed for this event."""
        allowed: List[str] = []
        for attr_name, value in vars(self).items():
            if attr_name.startswith("include_") and value is True:
                # Example: include_metrics -> "metrics"
                allowed.append(attr_name[len("include_"):])
        # Merge with *extra_fields*
        allowed.extend(self.extra_fields)
        # Return unique list while preserving order
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
    max_sample_predictions: int = 5  # not part of allowed_fields but useful


@dataclass
class LangGraphEventConfig(EventLogConfig):
    include_graph_state: bool = False
    include_node_name: bool = True
    include_transition_to: bool = True 
    include_status: bool = True 
    include_error: bool = True


@dataclass  
class StreamingEventConfig(EventLogConfig):
    include_user_input: bool = True
    include_accumulated_content: bool = True
    include_total_chunks: bool = True
    include_model: bool = True
    include_streaming_mode: bool = True
    include_session_id: bool = True
    include_chunk_content: bool = False  # Individual chunks, usually too verbose
    include_chunk_number: bool = True
    include_chunk_length: bool = True
    include_accumulated_length: bool = True
    include_duration_ms: bool = True 
