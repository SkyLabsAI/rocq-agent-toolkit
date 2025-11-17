from pathlib import Path

import pytest

import rocq_pipeline.find_tasks


def test_test_simple() -> None:
    tasks = rocq_pipeline.find_tasks.find_tasks(Path("examples/theories/test_simple.v"))
    assert len(tasks) == 2
    assert tasks == [{'locator': 'lemma:is_true','tags': ['proof']},{'locator': 'lemma:not_false','tags': ['proof']}]


@pytest.mark.skip(reason="temporary: requires pre-building the example")
def test_with_deps() -> None:
    tasks = rocq_pipeline.find_tasks.find_tasks(Path("examples/theories/with_dep.v"))
    assert len(tasks) == 1
    assert tasks == [{'locator': 'lemma:add_comm','tags': ['proof']}]

def test_factorial_longlong() -> None:
    tasks = rocq_pipeline.find_tasks.find_tasks(Path("../../../psi/data/brick_groundtruth/examples/loopcorpus/Factorial_longlong.v"), tagger=rocq_pipeline.find_tasks.my_tagger)
    assert len(tasks) == 4
    test_ok_inv_task = tasks[3]
    assert test_ok_inv_task['locator'] == 'lemma:test_ok_inv'
    tags = test_ok_inv_task['tags']
    assert set(tags) == {"proof",
                         "Arith.arith_simpl",
                         "rewrite",
                         "intros",
                         "wp_for",
                         "assert",
                         "go",
                         "lia",
                         "subst",
                         "verify_spec",
                         "specialize"}
