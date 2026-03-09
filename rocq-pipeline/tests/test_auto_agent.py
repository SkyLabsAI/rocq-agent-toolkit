import tempfile

import rocq_pipeline.task_runner as RAT
from rocq_pipeline.agent import AgentBuilder, AutoAgent, ProofAgent

from .util import make_repeated_tasks_str, make_task_str


def test_auto() -> None:
    with tempfile.TemporaryDirectory() as temp_dir:
        retcode = RAT.agent_main(
            AgentBuilder.of_agent(AutoAgent),
            [
                "--task-json",
                make_task_str("examples/theories/test_simple.v", "Lemma:is_true"),
                "--output-dir",
                temp_dir,
            ],
        )
    assert not retcode


def test_failure() -> None:
    with tempfile.TemporaryDirectory() as temp_dir:
        retcode = RAT.agent_main(
            AgentBuilder.of_agent(ProofAgent),
            [
                "--task-json",
                make_task_str("examples/theories/test_simple.v", "Lemma:is_true"),
                "--output-dir",
                temp_dir,
            ],
        )
    assert not retcode


def test_parallel_tasks() -> None:
    with tempfile.TemporaryDirectory() as temp_dir:
        num_tasks = 5
        retcode = RAT.agent_main(
            AgentBuilder.of_agent(AutoAgent),
            [
                "--task-json",
                make_repeated_tasks_str(
                    "examples/theories/test_simple.v",
                    "Lemma:is_true",
                    num_tasks=num_tasks,
                ),
                "--output-dir",
                temp_dir,
                f"-j{num_tasks}",
            ],
        )
    assert not retcode
