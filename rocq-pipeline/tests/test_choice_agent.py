import json
from rocq_pipeline.agent import ChoiceAgent
import rocq_pipeline.task_runner


def make_task(f: str, l: str):
    return json.dumps({"file": f, "locator": l})


class SimpleTactics(ChoiceAgent):
    def __init__(self):
        super().__init__(
            ["solve [ trivial ]", "tauto", "solve [ auto ]", "lia", "split"]
        )


def test_choice_agent():
    result = rocq_pipeline.task_runner.main(
        SimpleTactics,
        ["--task-json", make_task("examples/theories/test_simple.v", "lemma:is_true")],
    )
    assert result
