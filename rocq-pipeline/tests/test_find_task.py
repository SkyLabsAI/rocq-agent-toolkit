from pathlib import Path

import pytest
import rocq_pipeline.find_tasks
from rocq_dune_util import rocq_args_for


def test_test_simple() -> None:
    pdir = Path("examples")
    file = "theories/test_simple.v"
    path = pdir / Path(file)
    args = rocq_args_for(path)
    tasks = rocq_pipeline.find_tasks.find_tasks(pdir, path, args)
    assert len(tasks) == 2
    dict_tasks = [t.model_dump() for t in tasks]
    assert dict_tasks == [
        {
            "file": file,
            "locator": "Lemma:is_true",
            "tags": ["proof"],
        },
        {
            "file": file,
            "locator": "Lemma:not_false",
            "tags": ["proof"],
        },
    ]


@pytest.mark.skip(reason="temporary: requires pre-building the example")
def test_with_deps() -> None:
    pdir = Path("examples")
    file = "theories/with_dep.v"
    path = pdir / Path(file)
    args = rocq_args_for(path)
    tasks = rocq_pipeline.find_tasks.find_tasks(pdir, path, args)
    assert len(tasks) == 1
    dict_tasks = [t.model_dump() for t in tasks]
    assert dict_tasks == [
        {
            "name": None,
            "file": file,
            "locator": "Lemma:add_comm",
            "tags": ["proof"],
            "prompt": None,
        }
    ]
