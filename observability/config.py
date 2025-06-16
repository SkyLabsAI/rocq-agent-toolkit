"""
Observability Configuration

This module provides configuration management for the observability package.
It supports both environment-based and programmatic configuration with the
new framework-agnostic approach.
"""

from dataclasses import dataclass, field
from typing import Dict, Optional, Any
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
    
    # OpenTelemetry endpoints
    otlp_endpoint: str = "http://localhost:4317"
    otlp_insecure: bool = True
    
    # Feature toggles
    enable_tracing: bool = True
    enable_metrics: bool = True
    enable_logging: bool = True
    
    # LangSmith/LangChain integration
    enable_langsmith: bool = True
    langsmith_service_suffix: str = "langsmith"
    
    # Performance tuning
    batch_export_timeout_ms: int = 5000
    max_export_batch_size: int = 100
    metric_export_interval_ms: int = 10000
    
    # Logging configuration
    log_level: str = "INFO"
    log_format_json: bool = True
    
    # Global defaults for @trace decorator
    default_extractor: Optional[str] = None
    auto_metrics: bool = True
    trace_sampling_rate: float = 1.0  # Sample 100% by default
    
    # Resource attributes (added to all traces/metrics)
    resource_attributes: Dict[str, Any] = field(default_factory=dict)
    
    # Custom headers for OTLP export
    custom_headers: Dict[str, str] = field(default_factory=dict)
    
    @classmethod
    def from_environment(cls, **overrides) -> 'ObservabilityConfig':
        """
        Create configuration from environment variables.
        
        Environment variables:
        - OTEL_ENDPOINT → otlp_endpoint
        - OTEL_SERVICE_NAME → service_name  
        - OTEL_SERVICE_VERSION → service_version
        - OTEL_SERVICE_NAMESPACE → service_namespace
        - OTEL_ENVIRONMENT → environment
        - OTEL_LOG_LEVEL → log_level
        - OTEL_ENABLE_TRACING → enable_tracing
        - OTEL_ENABLE_METRICS → enable_metrics
        - OTEL_ENABLE_LOGGING → enable_logging
        - OTEL_TRACE_SAMPLING_RATE → trace_sampling_rate
        - OTEL_DEFAULT_EXTRACTOR → default_extractor
        - OTEL_ENABLE_LANGSMITH → enable_langsmith
        - OTEL_LANGSMITH_SERVICE_SUFFIX → langsmith_service_suffix
        
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
        env_config = {
            'service_name': os.getenv('OTEL_SERVICE_NAME', 'unknown-service'),
            'service_version': os.getenv('OTEL_SERVICE_VERSION', 'unknown'),
            'service_namespace': os.getenv('OTEL_SERVICE_NAMESPACE', 'default'),
            'environment': os.getenv('OTEL_ENVIRONMENT'),
            'otlp_endpoint': os.getenv('OTEL_ENDPOINT', 'http://localhost:4317'),
            'log_level': os.getenv('OTEL_LOG_LEVEL', 'INFO'),
            'enable_tracing': os.getenv('OTEL_ENABLE_TRACING', 'true').lower() == 'true',
            'enable_metrics': os.getenv('OTEL_ENABLE_METRICS', 'true').lower() == 'true',
            'enable_logging': os.getenv('OTEL_ENABLE_LOGGING', 'true').lower() == 'true',
            'default_extractor': os.getenv('OTEL_DEFAULT_EXTRACTOR'),
            'trace_sampling_rate': float(os.getenv('OTEL_TRACE_SAMPLING_RATE', '1.0')),
            'enable_langsmith': os.getenv('OTEL_ENABLE_LANGSMITH', 'true').lower() == 'true',
            'langsmith_service_suffix': os.getenv('OTEL_LANGSMITH_SERVICE_SUFFIX', 'langsmith'),
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
    sensitive_headers: list = field(default_factory=lambda: [
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