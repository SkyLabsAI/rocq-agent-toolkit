import tempfile

import rocq_pipeline.task_runner
from rocq_pipeline.agent import ChoiceAgent

from .util import make_task


class SimpleTactics(ChoiceAgent):
    def __init__(self) -> None:
        super().__init__([
            "solve [ trivial ]",
            "tauto",
            "solve [ auto ]",
            "lia",
            "split"
        ])


def test_choice_agent() -> None:
    with tempfile.TemporaryDirectory() as temp_dir:
        result = rocq_pipeline.task_runner.main(
            SimpleTactics,
            ["--task-json", make_task("examples/theories/test_simple.v", "lemma:is_true"),
             "--output-dir", temp_dir],
        )
    assert result
