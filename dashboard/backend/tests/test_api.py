from backend.db_models import AgentClassProvenance, AgentProvenance, Run, TaskResultDB
from sqlmodel import Session, select


def test_root_ok(client):
    resp = client.get("/")
    assert resp.status_code == 200
    body = resp.json()
    assert body["status"] == "running"


def test_health_empty_db_returns_0_agents(client):
    resp = client.get("/api/health")
    assert resp.status_code == 200
    assert resp.json() == {"status": "healthy", "total_agents": 0}


def test_ingest_empty_list_returns_400(client):
    resp = client.post("/api/ingest", params={"source_file_name": "x.jsonl"}, json=[])
    assert resp.status_code == 400
    assert "No task results provided" in resp.json()["detail"]


def test_ingest_invalid_body_returns_422(client):
    resp = client.post(
        "/api/ingest",
        params={"source_file_name": "x.jsonl"},
        json=[{"not": "a taskresult"}],
    )
    assert resp.status_code == 422


def test_ingest_happy_path_persists_and_list_agents_and_runs(
    client, engine, make_task_result_payload
):
    run_id = "00000000-0000-0000-0000-000000000100"
    items = [
        make_task_result_payload(run_id=run_id, task_id="t1", status="Success"),
        make_task_result_payload(run_id=run_id, task_id="t2", status="Failure"),
    ]

    resp = client.post(
        "/api/ingest", params={"source_file_name": "x.jsonl"}, json=items
    )
    assert resp.status_code == 200
    body = resp.json()
    assert body["success"] is True
    assert body["runs_ingested"] == 1
    assert body["tasks_ingested"] == 2

    agents = client.get("/api/agents/class")
    assert agents.status_code == 200
    agents_data = agents.json()
    assert len(agents_data) > 0
    # With fallback, cls_name will be the checksum
    assert agents_data[0]["cls_name"] == "cls_checksum_test"
    assert agents_data[0]["total_runs"] == 1

    # Use the cls_checksum to get runs (the endpoint expects cls_checksum, not name)
    runs = client.get(f"/api/agents/class/{agents_data[0]['cls_checksum']}/runs")
    assert runs.status_code == 200
    assert runs.json()[0]["run_id"] == run_id
    assert runs.json()[0]["total_tasks"] == 2

    # Spot-check DB state (integration-level confidence)
    with Session(engine) as s:
        assert len(s.exec(select(AgentProvenance)).all()) == 1
        assert len(s.exec(select(AgentClassProvenance)).all()) == 1
        assert len(s.exec(select(Run)).all()) == 1
        assert len(s.exec(select(TaskResultDB)).all()) == 2


def test_list_runs_by_agent_unknown_returns_404(client):
    resp = client.get("/api/agents/does-not-exist/runs")
    assert resp.status_code == 404
