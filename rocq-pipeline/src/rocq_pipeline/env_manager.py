"""
Environment manager for Rocq Pipeline
Defines the abstract Environment interface and Registry.
"""

import os
from abc import ABC, abstractmethod
from pathlib import Path

from observability import get_logger

logger = get_logger("env_manager")


class Environment(ABC):
    """
    Abstract base class for all execution environments.
    """

    @abstractmethod
    def setup(self) -> bool:
        """Prepare the environment (start services, check connectivity)
        Basic Callback to Run before the task is executed."""
        pass

    @abstractmethod
    def post_run(self, result_file: Path) -> None:
        """Handle results (upload them, move them, or just log location).
        Basic Callback to Run after the task is executed."""
        pass

    @abstractmethod
    def get_otlp_endpoint(self) -> str:
        """Return the OTLP endpoint for this environment."""
        pass


class NoOpEnvironment(Environment):
    """Default environment that does nothing."""

    def setup(self) -> bool:
        return True

    def post_run(self, result_file: Path) -> None:
        pass

    def get_otlp_endpoint(self) -> str:
        return os.getenv("LOG_OTLP_ENDPOINT", "http://0.0.0.0:4317")


class EnvironmentRegistry:
    """Registry for Environment implementations."""
    _registry: dict[str, type[Environment]] = {}

    @classmethod
    def register(cls, name: str, env_class: type[Environment]) -> None:
        cls._registry[name] = env_class

    @classmethod
    def get(cls, name: str) -> type[Environment]:
        """Get an environment class by name. Defaults to NoOpEnvironment."""
        return cls._registry.get(name, NoOpEnvironment)


# Register default
EnvironmentRegistry.register("none", NoOpEnvironment)


# Try to load internal extensions to register environments
try:
    import rocq_pipeline.internal.envs as _  # noqa: F401
except ImportError:
    print("No internal extensions found")
    pass
