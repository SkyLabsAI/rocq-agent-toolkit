import json
from rocq_pipeline.agent import Agent
from rocq_pipeline.auto_agent import AutoAgent
from rocq_pipeline.task_runner import task_main

def make_task(f: str, l: str):
    return json.dumps({ 'file': f, 'locator': l })

def test_auto():
    result = task_main(AutoAgent, ['--task-json', make_task('examples/theories/test_simple.v', 'lemma:is_true') ])
    assert result

def test_failure():
    result = task_main(Agent, ['--task-json', make_task('examples/theories/test_simple.v', 'lemma:is_true') ])
    assert result
