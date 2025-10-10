import json
from psi_agents.hammer_agent import HammerAgent
from rocq_pipeline.task_runner import task_main

def make_task(f: str, l: str):
    return json.dumps({ 'file': f, 'locator': l })

def test_failure():
    result = task_main(HammerAgent, ['--task-json', make_task('examples/theories/test_brick.v', 'lemma:test_ok') ])
    assert result
