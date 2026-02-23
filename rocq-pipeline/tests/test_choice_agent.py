import tempfile

import rocq_pipeline.task_runner
from rocq_pipeline.agent import AgentBuilder, ChoiceAgent

from .util import make_task_str


class SimpleTactics(ChoiceAgent):
    def __init__(self) -> None:
        super().__init__(
            ["solve [ trivial ]", "tauto", "solve [ auto ]", "lia", "split"]
        )


def test_choice_agent() -> None:
    with tempfile.TemporaryDirectory() as temp_dir:
        result = rocq_pipeline.task_runner.agent_main(
            AgentBuilder.of_agent(SimpleTactics),
            [
                "--task-json",
                make_task_str("examples/theories/test_simple.v", None, "Lemma:is_true"),
                "--output-dir",
                temp_dir,
            ],
        )
    assert result
