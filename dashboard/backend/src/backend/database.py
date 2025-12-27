"""
Database engine and session management for the RAT dashboard backend.

This module is responsible for:
- Creating the SQLModel engine
- Initializing the schema (creating tables)
- Providing a FastAPI-friendly session dependency
"""

from collections.abc import Iterator

from sqlmodel import Session, SQLModel, create_engine

from backend.config import settings

# Create a global SQLModel engine.
# We intentionally use the synchronous engine here; FastAPI will run
# the blocking DB work in a threadpool when used from async endpoints.
engine = create_engine(
    settings.database_url,
    echo=settings.database_echo,
    pool_pre_ping=True,
)


def init_db() -> None:
    """
    Initialize the database schema.

    This should be called at application startup (e.g. from FastAPI's
    lifespan/startup handler) to ensure that all tables defined in
    `db_models.py` exist.
    """
    # Import models so that SQLModel is aware of them before metadata.create_all
    from backend import db_models  # noqa: F401  # pylint: disable=unused-import

    SQLModel.metadata.create_all(bind=engine)


def get_session() -> Iterator[Session]:
    """
    FastAPI dependency that provides a database session.

    Usage:
        from fastapi import Depends
        from sqlmodel import Session

        @router.get("/agents")
        def list_agents(session: Session = Depends(get_session)):
            ...
    """
    with Session(engine) as session:
        yield session
