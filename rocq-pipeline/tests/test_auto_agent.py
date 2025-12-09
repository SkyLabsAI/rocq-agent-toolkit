import tempfile

import rocq_pipeline.task_runner
from rocq_pipeline.agent import AgentBuilder, AutoAgent, ProofAgent

from .util import make_repeated_tasks_str, make_task_str


def test_auto() -> None:
    with tempfile.TemporaryDirectory() as temp_dir:
        result = rocq_pipeline.task_runner.agent_main(
            AgentBuilder.of_agent(AutoAgent),
            [
                "--task-json",
                make_task_str("examples/theories/test_simple.v", "lemma:is_true"),
                "--output-dir",
                temp_dir,
            ],
        )
    assert result


def test_failure() -> None:
    with tempfile.TemporaryDirectory() as temp_dir:
        result = rocq_pipeline.task_runner.agent_main(
            AgentBuilder.of_agent(ProofAgent),
            [
                "--task-json",
                make_task_str("examples/theories/test_simple.v", "lemma:is_true"),
                "--output-dir",
                temp_dir,
            ],
        )
    assert result


def test_parallel_tasks() -> None:
    with tempfile.TemporaryDirectory() as temp_dir:
        num_tasks = 5
        result = rocq_pipeline.task_runner.agent_main(
            AgentBuilder.of_agent(AutoAgent),
            [
                "--task-json",
                make_repeated_tasks_str(
                    "examples/theories/test_simple.v",
                    "lemma:is_true",
                    num_tasks=num_tasks,
                ),
                "--output-dir",
                temp_dir,
                f"-j{num_tasks}",
            ],
        )
    assert result
