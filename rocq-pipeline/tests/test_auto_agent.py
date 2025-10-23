import json
from rocq_pipeline.agent import Agent
from rocq_pipeline.auto_agent import AutoAgent
import rocq_pipeline.task_runner


def make_task(file_path: str, locator: str):
    return json.dumps({'file': file_path, 'locator': locator})


def test_auto():
    result = rocq_pipeline.task_runner.main(AutoAgent, [
        '--task-json',
        make_task('examples/theories/test_simple.v', 'lemma:is_true')
    ])
    assert result


def test_failure():
    result = rocq_pipeline.task_runner.main(Agent, [
        '--task-json',
        make_task('examples/theories/test_simple.v', 'lemma:is_true')
    ])
    assert result
