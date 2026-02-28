import json

from rocq_pipeline.task_modifiers import InsertCommand
from rocq_pipeline.task_modifiers.task_mod import of_string


def test_parses():
    # check defaults
    assert of_string(
        json.dumps({"insert_command": {"commands": []}})
    ) == InsertCommand.make(commands=[])
    assert of_string(
        json.dumps({"insert_command": {"commands": [], "ghost": True}})
    ) == InsertCommand.make(commands=[], ghost=True)

    for gh in [True, False]:
        for at in [True, False]:
            assert of_string(
                json.dumps(
                    {"insert_command": {"commands": [], "ghost": gh, "attempt": at}}
                )
            ) == InsertCommand.make(commands=[], ghost=gh, attempt=at)
