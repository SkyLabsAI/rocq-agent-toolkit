from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, Optional


@dataclass
class CoreConfig:
    """
    Core configuration for observability features.
    """

    # Service identification
    service_name: str
    service_version: str = "unknown"
    service_namespace: str = "default"
    environment: Optional[str] = None

    # User/Session identification (optional)
    user_id: Optional[str] = None
    session_id: Optional[str] = None

    # Resource attributes
    resource_attributes: Dict[str, Any] = field(default_factory=dict)

    # OTLP Endpoint Configuration
    otlp_endpoint: str = "http://localhost:4317"
    otlp_insecure: bool = True

    # Custom headers for OTLP export
    custom_headers: Dict[str, str] = field(default_factory=dict)
