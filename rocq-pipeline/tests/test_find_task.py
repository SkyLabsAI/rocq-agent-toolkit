from pathlib import Path

import rocq_pipeline.find_tasks


def test_test_simple() -> None:
    tasks = rocq_pipeline.find_tasks.find_tasks(Path("examples/theories/test_simple.v"))
    assert len(tasks) == 2
    assert tasks == [{'locator': 'lemma:is_true','tags': ['proof']},{'locator': 'lemma:not_false','tags': ['proof']}]

def test_with_deps() -> None:
    tasks = rocq_pipeline.find_tasks.find_tasks(Path("examples/theories/with_dep.v"))
    assert len(tasks) == 1
    assert tasks == [{'locator': 'lemma:add_comm','tags': ['proof']}]
