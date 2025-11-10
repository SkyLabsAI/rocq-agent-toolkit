import pytest
from fastapi.testclient import TestClient
from unittest.mock import MagicMock, patch
from backend.models import AgentInfo, RunInfo, RunDetailsResponse, TaskResult
import os
import json
from pathlib import Path

# Set env var before importing app
os.environ["JSONL_RESULTS_PATH"] = "/tmp/mock_results"
os.environ["OBSERVABILITY_URL"] = "http://localhost:3100"

from backend.main import app
from backend.data_access import DataStore

@pytest.fixture
def client():
    with patch("backend.main.data_store") as mock_store:
        yield TestClient(app)

@pytest.fixture
def mock_jsonl_data():
    return [
        {
            "run_id": "run1",
            "agent_name": "agent1",
            "task_id": "task1",
            "status": "Success",
            "timestamp_utc": "2023-01-01T12:00:00Z",
            "task_kind": "kind1",
            "metrics": {
                "llm_invocation_count": 0,
                "token_counts": {"input_tokens": 0, "output_tokens": 0, "total_tokens": 0},
                "resource_usage": {"execution_time_sec": 0.0, "cpu_time_sec": 0.0, "gpu_time_sec": 0.0},
                "custom": None
            },
            "results": "",
        },
        {
            "run_id": "run1",
            "agent_name": "agent1",
            "task_id": "task2",
            "status": "Failure",
            "timestamp_utc": "2023-01-01T12:01:00Z",
            "task_kind": "kind1",
            "metrics": {
                "llm_invocation_count": 0,
                "token_counts": {"input_tokens": 0, "output_tokens": 0, "total_tokens": 0},
                "resource_usage": {"execution_time_sec": 0.0, "cpu_time_sec": 0.0, "gpu_time_sec": 0.0},
                "custom": None
            },
            "results": "",
        },
        {
            "run_id": "run2",
            "agent_name": "agent2",
            "task_id": "task3",
            "status": "Success",
            "timestamp_utc": "2023-01-02T10:00:00Z",
            "task_kind": "kind2",
            "metrics": {
                "llm_invocation_count": 0,
                "token_counts": {"input_tokens": 0, "output_tokens": 0, "total_tokens": 0},
                "resource_usage": {"execution_time_sec": 0.0, "cpu_time_sec": 0.0, "gpu_time_sec": 0.0},
                "custom": None
            },
            "results": "",
        },
        {
            "run_id": "run3",
            "agent_name": "agent1",
            "task_id": "task4",
            "status": "Success",
            "timestamp_utc": "2023-01-03T11:00:00Z",
            "task_kind": "kind1",
            "metrics": {
                "llm_invocation_count": 0,
                "token_counts": {"input_tokens": 0, "output_tokens": 0, "total_tokens": 0},
                "resource_usage": {"execution_time_sec": 0.0, "cpu_time_sec": 0.0, "gpu_time_sec": 0.0},
                "custom": None
            },
            "results": "",
        },
    ]

@pytest.fixture
def temp_jsonl_dir(tmp_path, mock_jsonl_data):
    data_dir = tmp_path / "jsonl_data"
    data_dir.mkdir()
    
    file1_data = mock_jsonl_data[:2]
    file2_data = mock_jsonl_data[2:]

    with open(data_dir / "file1.jsonl", "w") as f:
        for item in file1_data:
            f.write(json.dumps(item) + "\n")
            
    with open(data_dir / "file2.jsonl", "w") as f:
        for item in file2_data:
            f.write(json.dumps(item) + "\n")
            
    (data_dir / "empty.jsonl").touch()
    with open(data_dir / "invalid.jsonl", "w") as f:
        f.write("this is not json\n")
        f.write(json.dumps(mock_jsonl_data[0]) + "\n")

    return data_dir

def test_list_agents(client):
    with patch("backend.main.data_store") as mock_store:
        mock_store.get_all_agents.return_value = [
            AgentInfo(agent_name="agent1", total_runs=2),
            AgentInfo(agent_name="agent2", total_runs=1),
        ]
        response = client.get("/api/agents")
        assert response.status_code == 200
        data = response.json()
        assert len(data) == 2
        assert data[0]["agent_name"] == "agent1"

def test_list_runs_by_agent(client):
    with patch("backend.main.data_store") as mock_store:
        mock_store.get_runs_by_agent.return_value = [
            RunInfo(run_id="run1", agent_name="agent1", timestamp_utc="2023-01-01T12:00:00Z", total_tasks=2, success_count=1, failure_count=1)
        ]
        mock_store.get_all_agents.return_value = [AgentInfo(agent_name="agent1", total_runs=1)]
        response = client.get("/api/agents/agent1/runs")
        assert response.status_code == 200
        data = response.json()
        assert len(data) == 1

def test_get_run_details(client):
    with patch("backend.main.data_store") as mock_store:
        mock_task = TaskResult(
            run_id="run1", agent_name="agent1", task_id="task1", status="Success", timestamp_utc="2023-01-01T12:00:00Z", 
            task_kind="kind1", 
            metrics={
                "llm_invocation_count": 0,
                "token_counts": {"input_tokens": 0, "output_tokens": 0, "total_tokens": 0},
                "resource_usage": {"execution_time_sec": 0.0, "cpu_time_sec": 0.0, "gpu_time_sec": 0.0},
                "custom": None
            },
            results=""
        )
        mock_store.get_run_details.return_value = [
            RunDetailsResponse(run_id="run1", agent_name="agent1", total_tasks=1, tasks=[mock_task])
        ]
        response = client.get("/api/runs/details?run_ids=run1")
        assert response.status_code == 200
        data = response.json()
        assert len(data[0]["tasks"]) == 1

@patch("httpx.AsyncClient")
def test_get_observability_logs(mock_async_client, client):
    mock_response = MagicMock()
    mock_response.status_code = 200
    mock_response.json.return_value = {
        "status": "success", "data": {"result": [{"stream": {"new_label": "new_value"}, "values": [["1", "log"]]}]}
    }
    instance = mock_async_client.return_value.__aenter__.return_value
    instance.get.return_value = mock_response

    response = client.get("/api/observability/logs?run_id=run1&task_id=task1")
    assert response.status_code == 200
    data = response.json()
    assert data["total_labels"] > 0

def test_load_from_directory(temp_jsonl_dir):
    data_store = DataStore()
    count = data_store.load_from_directory(temp_jsonl_dir)
    assert count == 5
    assert len(data_store.task_results) == 5
    assert "agent1" in data_store._agents
    assert "agent2" in data_store._agents

def test_get_all_agents(temp_jsonl_dir):
    data_store = DataStore()
    data_store.load_from_directory(temp_jsonl_dir)
    agents = data_store.get_all_agents()
    assert len(agents) == 2
    for agent in agents:
        if agent.agent_name == "agent1":
            assert agent.total_runs == 2
        if agent.agent_name == "agent2":
            assert agent.total_runs == 1

def test_get_runs_by_agent_data_access(temp_jsonl_dir):
    data_store = DataStore()
    data_store.load_from_directory(temp_jsonl_dir)
    runs = data_store.get_runs_by_agent("agent1")
    assert len(runs) == 2

def test_get_run_details_data_access(temp_jsonl_dir):
    data_store = DataStore()
    data_store.load_from_directory(temp_jsonl_dir)
    details = data_store.get_run_details(["run1"])
    assert len(details) == 1
    assert details[0].total_tasks == 3
