from backend.dal import ingest_task_results
from backend.db_models import (
    AgentClassProvenance,
    AgentProvenance,
    Dataset,
    Run,
    Tag,
    Task,
    TaskResultDB,
)
from backend.models import TaskResult
from sqlmodel import Session, select


def _to_task_result(payload: dict) -> TaskResult:
    return TaskResult.model_validate(payload)


async def test_ingest_creates_agent_dataset_run_tasks_results_and_tags(
    db_session: Session, make_task_result_payload
):
    run_id = "00000000-0000-0000-0000-000000000010"

    payloads = [
        make_task_result_payload(
            run_id=run_id,
            task_id="t1",
            status="Success",
            timestamp_utc="2025-01-01T00:00:02Z",
            tags={"difficulty": "easy", "suite": "smoke"},
            total_tokens=10,
            input_tokens=4,
            output_tokens=6,
            execution_time_sec=1.0,
        ),
        make_task_result_payload(
            run_id=run_id,
            task_id="t2",
            status="Failure",
            timestamp_utc="2025-01-01T00:00:01Z",  # earlier => run timestamp should match this
            tags={"difficulty": "easy"},
            total_tokens=20,
            input_tokens=7,
            output_tokens=13,
            execution_time_sec=2.0,
            failure_reason=["boom"],
        ),
    ]

    stats = await ingest_task_results(
        db_session,
        [_to_task_result(p) for p in payloads],
        source_file_name="file.jsonl",
    )
    db_session.commit()

    assert stats == {"runs_ingested": 1, "tasks_ingested": 2}

    # Check that agent provenance was created (fallback uses checksum as name)
    agent_instance = db_session.exec(
        select(AgentProvenance).where(
            AgentProvenance.agent_checksum == "agent_checksum_test"
        )
    ).first()
    assert agent_instance is not None
    # With fallback, name will be the checksum
    assert agent_instance.agent_checksum == "agent_checksum_test"

    # Check that agent class provenance was created
    agent_class = db_session.exec(
        select(AgentClassProvenance).where(
            AgentClassProvenance.cls_checksum == "cls_checksum_test"
        )
    ).first()
    assert agent_class is not None
    assert agent_class.cls_checksum == "cls_checksum_test"

    dataset = db_session.exec(select(Dataset)).one()
    assert dataset.name == "ds1"

    tasks = db_session.exec(select(Task).order_by(Task.id)).all()
    assert [t.id for t in tasks] == ["t1", "t2"]

    run = db_session.exec(select(Run)).one()
    assert str(run.id) == run_id
    assert run.total_tasks == 2
    assert run.success_count == 1
    assert run.failure_count == 1
    assert run.success_rate == 0.5
    assert run.total_tokens == 30
    assert run.total_input_tokens == 11
    assert run.total_output_tokens == 19
    assert run.total_execution_time_sec == 3.0
    assert run.source_file_name == "file.jsonl"
    # earliest timestamp is the second task
    assert run.timestamp_utc.isoformat().startswith("2025-01-01T00:00:01")

    results = db_session.exec(select(TaskResultDB).order_by(TaskResultDB.task_id)).all()
    assert [r.task_id for r in results] == ["t1", "t2"]
    assert results[1].failure_reason == ["boom"]

    tags = db_session.exec(select(Tag).order_by(Tag.key, Tag.value)).all()
    assert [(t.key, t.value) for t in tags] == [
        ("difficulty", "easy"),
        ("suite", "smoke"),
    ]


async def test_reingest_replaces_task_results_for_same_run(
    db_session: Session, make_task_result_payload
):
    run_id = "00000000-0000-0000-0000-000000000020"

    first = [
        _to_task_result(
            make_task_result_payload(run_id=run_id, task_id="t1", status="Success")
        ),
        _to_task_result(
            make_task_result_payload(run_id=run_id, task_id="t2", status="Failure")
        ),
    ]
    await ingest_task_results(db_session, first, source_file_name="first.jsonl")
    db_session.commit()

    assert db_session.exec(select(TaskResultDB)).all()

    # Re-ingest same run_id with a different task set; old results should be deleted.
    second = [
        _to_task_result(
            make_task_result_payload(
                run_id=run_id, task_id="t3", status="Success", total_tokens=999
            )
        ),
    ]
    await ingest_task_results(db_session, second, source_file_name="second.jsonl")
    db_session.commit()

    results = db_session.exec(select(TaskResultDB).order_by(TaskResultDB.task_id)).all()
    assert [r.task_id for r in results] == ["t3"]

    run = db_session.exec(select(Run)).one()
    assert run.total_tasks == 1
    assert run.total_tokens == 999
    assert run.source_file_name == "second.jsonl"
