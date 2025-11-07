"""
Configuration management for the FastAPI backend.
"""
from pathlib import Path
from pydantic_settings import BaseSettings, SettingsConfigDict


class Settings(BaseSettings):
    """Application settings loaded from environment variables."""

    # Path to JSONL results directory
    jsonl_results_path: str

    # Observability stack port
    observability_url: str = "http://0.0.0.0:3100"
    log_query_time_delta_days: int = 7

    # Server configuration
    server_host: str = "0.0.0.0"
    server_port: int = 8000

    model_config = SettingsConfigDict(
        env_file=".env", env_file_encoding="utf-8", case_sensitive=False
    )

    def get_results_path(self) -> Path:
        """Get the JSONL results path as a Path object."""
        return Path(self.jsonl_results_path)


# Global settings instance
settings = Settings()
