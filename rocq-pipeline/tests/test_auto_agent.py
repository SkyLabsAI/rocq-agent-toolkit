import tempfile

import rocq_pipeline.task_runner
from rocq_pipeline.agent import Agent
from rocq_pipeline.auto_agent import AutoAgent

from .util import make_task


def test_auto() -> None:
    with tempfile.TemporaryDirectory() as temp_dir:
        result = rocq_pipeline.task_runner.main(
            AutoAgent,
            ["--task-json", make_task("examples/theories/test_simple.v", "lemma:is_true"),
             "--output-dir", temp_dir],
        )
    assert result


def test_failure() -> None:
    with tempfile.TemporaryDirectory() as temp_dir:
        result = rocq_pipeline.task_runner.main(
            Agent,
            ["--task-json", make_task("examples/theories/test_simple.v", "lemma:is_true"),
             "--output-dir", temp_dir],
        )
    assert result
