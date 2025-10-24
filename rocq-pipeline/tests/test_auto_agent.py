import rocq_pipeline.task_runner
from rocq_pipeline.agent import Agent
from rocq_pipeline.auto_agent import AutoAgent

from .util import make_task


def test_auto() -> None:
    result = rocq_pipeline.task_runner.main(
        AutoAgent,
        ["--task-json", make_task("examples/theories/test_simple.v", "lemma:is_true")],
    )
    assert result


def test_failure() -> None:
    result = rocq_pipeline.task_runner.main(
        Agent,
        ["--task-json", make_task("examples/theories/test_simple.v", "lemma:is_true")],
    )
    assert result
