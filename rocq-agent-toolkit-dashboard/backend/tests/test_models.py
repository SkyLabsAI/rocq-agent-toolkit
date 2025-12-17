import json

from backend.models import TaskResult


def _base_payload(*, results):
    return {
        "run_id": "00000000-0000-0000-0000-000000000001",
        "task_kind": "kind",
        "task_id": "t1",
        "dataset_id": "ds1",
        "timestamp_utc": "2025-01-01T00:00:00Z",
        "agent_name": "agentA",
        "status": "Success",
        "metrics": {
            "llm_invocation_count": 1,
            "token_counts": {"input_tokens": 1, "output_tokens": 2, "total_tokens": 3},
            "resource_usage": {
                "execution_time_sec": 0.1,
                "cpu_time_sec": 0.1,
                "gpu_time_sec": 0.0,
            },
            "custom": None,
        },
        "metadata": {"tags": {}},
        "results": results,
        "failure_reason": None,
    }

# Different support for the results field in the TaskResult model.
# Is for the backward compatibility with the old format.
def test_taskresult_results_keeps_dict():
    payload = _base_payload(results={"a": 1})
    tr = TaskResult.model_validate(payload)
    assert tr.results == {"a": 1}


def test_taskresult_results_parses_json_string_dict():
    payload = _base_payload(results=json.dumps({"x": {"y": 2}}))
    tr = TaskResult.model_validate(payload)
    assert tr.results == {"x": {"y": 2}}


def test_taskresult_results_wraps_non_json_string_for_backcompat():
    payload = _base_payload(results="some old string format")
    tr = TaskResult.model_validate(payload)
    assert tr.results == {"side_effects": {"doc_interaction": "some old string format"}}


