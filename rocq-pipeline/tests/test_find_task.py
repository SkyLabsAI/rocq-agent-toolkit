from pathlib import Path

import pytest
import rocq_pipeline.find_tasks


def test_test_simple() -> None:
    tasks = rocq_pipeline.find_tasks.find_tasks(Path("examples/theories/test_simple.v"))
    assert len(tasks) == 2
    assert tasks == [
        {"locator": "Lemma:is_true", "tags": ["proof"]},
        {"locator": "Lemma:not_false", "tags": ["proof"]},
    ]


@pytest.mark.skip(reason="temporary: requires pre-building the example")
def test_with_deps() -> None:
    tasks = rocq_pipeline.find_tasks.find_tasks(Path("examples/theories/with_dep.v"))
    assert len(tasks) == 1
    assert tasks == [{"locator": "Lemma:add_comm", "tags": ["proof"]}]


def test_factorial_longlong() -> None:
    tasks = rocq_pipeline.find_tasks.find_tasks(
        Path("tests/Factorial_longlong.v"), tagger=rocq_pipeline.find_tasks.my_tagger
    )
    assert len(tasks) == 2
    test_ok_inv_task = tasks[1]
    assert test_ok_inv_task["locator"] == "Lemma:test_ok_inv"
    tags = test_ok_inv_task["tags"]
    assert set(tags) == {
        "proof",
        "qed",
        "Arith.arith_simpl",
        "rewrite",
        "intros",
        "wp_for-loopinv",
        "assert",
        "go",
        "lia",
        "verify_spec",
        "specialize",
        "NumTactics=18",
        "UnmatchedTactics=['+', '{', '}']",
    }
