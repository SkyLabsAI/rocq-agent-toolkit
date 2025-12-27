import uuid
from collections.abc import Callable, Generator

import pytest
from backend.database import get_session
from fastapi.testclient import TestClient
from sqlalchemy.pool import StaticPool
from sqlmodel import Session, SQLModel, create_engine


@pytest.fixture()
def engine():
    """
    SQLite in-memory engine shared across threads (TestClient runs the app in a thread).
    Function-scoped to keep DB state isolated per test.
    """
    engine = create_engine(
        "sqlite://",
        connect_args={"check_same_thread": False},
        poolclass=StaticPool,
    )
    # Ensure models are imported so SQLModel.metadata is populated.
    import backend.db_models  # noqa: F401

    SQLModel.metadata.create_all(engine)
    return engine


@pytest.fixture()
def db_session(engine) -> Generator[Session]:
    with Session(engine) as session:
        yield session


@pytest.fixture()
def make_task_result_payload() -> Callable[..., dict]:
    """
    Factory for valid TaskResult payloads for API requests.
    Keeps tests readable and ensures fields required by Pydantic are present.
    """

    def _make(
        *,
        run_id: str | None = None,
        task_id: str = "t1",
        task_kind: str = "kind",
        dataset_id: str | None = "ds1",
        timestamp_utc: str = "2025-01-01T00:00:00Z",
        agent_name: str = "agentA",
        agent_cls_checksum: str = "cls_checksum_test",
        agent_checksum: str = "agent_checksum_test",
        status: str = "Success",
        tags: dict[str, str] | None = None,
        results: object | None = None,
        failure_reason: list[str] | None = None,
        input_tokens: int = 1,
        output_tokens: int = 2,
        total_tokens: int = 3,
        execution_time_sec: float = 0.1,
        cpu_time_sec: float = 0.1,
        gpu_time_sec: float = 0.0,
        llm_invocation_count: int = 1,
    ) -> dict:
        rid = run_id or str(uuid.uuid4())
        payload: dict = {
            "run_id": rid,
            "task_kind": task_kind,
            "task_id": task_id,
            "dataset_id": dataset_id,
            "timestamp_utc": timestamp_utc,
            "agent_name": agent_name,
            "agent_cls_checksum": agent_cls_checksum,
            "agent_checksum": agent_checksum,
            "status": status,
            "metrics": {
                "llm_invocation_count": llm_invocation_count,
                "token_counts": {
                    "input_tokens": input_tokens,
                    "output_tokens": output_tokens,
                    "total_tokens": total_tokens,
                },
                "resource_usage": {
                    "execution_time_sec": execution_time_sec,
                    "cpu_time_sec": cpu_time_sec,
                    "gpu_time_sec": gpu_time_sec,
                },
                "custom": None,
            },
            "metadata": {"tags": tags or {}},
            "results": results,
            "failure_reason": failure_reason,
        }
        return payload

    return _make


@pytest.fixture()
def client(engine, monkeypatch) -> Generator[TestClient]:
    """
    FastAPI TestClient wired to the SQLite engine via dependency overrides.

    Also disables startup DB init against Postgres and disables S3 backup.
    """
    # Import inside fixture so monkeypatching affects the already-imported module globals.
    from backend.main import app

    # Avoid touching the production database on app startup.
    monkeypatch.setattr("backend.main.init_db", lambda: None)

    # Disable S3 uploads entirely during tests (external integration not under test).
    monkeypatch.setattr("backend.main.upload_bytes_to_s3", lambda **kwargs: None)

    def _override_get_session() -> Generator[Session]:
        with Session(engine) as session:
            yield session

    app.dependency_overrides[get_session] = _override_get_session
    try:
        with TestClient(app) as c:
            yield c
    finally:
        app.dependency_overrides.clear()
