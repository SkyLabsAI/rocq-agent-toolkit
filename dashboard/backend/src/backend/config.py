"""
Configuration management for the FastAPI backend.
"""

from pydantic_settings import BaseSettings, SettingsConfigDict


class Settings(BaseSettings):
    """Application settings loaded from environment variables."""

    # Database configuration
    # TODO: Database can communicate internally with the docker network.
    # No need for external localhost/network communication.
    postgres_host: str = "localhost"
    postgres_port: int = 5433
    postgres_user: str = "rat_user"
    postgres_password: str = "rat_password"
    postgres_db: str = "rat_db"
    # Default to a synchronous SQLAlchemy/SQLModel URL using the modern
    # psycopg (v3) driver. This can be overridden via the DATABASE_URL
    # environment variable for deployments.
    database_url: str = (
        f"postgresql+psycopg://{postgres_user}:{postgres_password}@"
        f"{postgres_host}:{postgres_port}/{postgres_db}"
    )
    database_echo: bool = False  # SQL logging

    # Observability stack port
    observability_url: str = "http://0.0.0.0:3110"
    # Legacy days-based setting (kept for backwards compatibility, not used directly)
    log_query_time_delta_days: int = 7
    # Time window (in hours) around the task timestamp used when querying Loki
    log_query_time_delta_hours: int = 12

    # Server configuration
    server_host: str = "0.0.0.0"
    server_port: int = 8010
    log_level: str = "info"

    # AWS S3 Configuration (Optional - for backup)
    AWS_ACCESS_KEY_ID: str | None = None
    AWS_SECRET_ACCESS_KEY: str | None = None
    AWS_REGION: str | None = None
    S3_BUCKET_NAME: str | None = None

    model_config = SettingsConfigDict(
        env_file=".env", env_file_encoding="utf-8", case_sensitive=False
    )


# Global settings instance
settings = Settings()
