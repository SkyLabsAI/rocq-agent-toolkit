from collections.abc import Callable, Generator
from contextlib import contextmanager
from pathlib import Path

import pytest
from rocq_doc_manager import RocqCursor, RocqDocManager
from rocq_pipeline.agent.proof import trace_cursor


@contextmanager
def build_both(verbose: bool) -> Generator[tuple[RocqCursor, RocqCursor]]:
    rdm = RocqDocManager(
        [],
        str(Path(__file__).parent / "test.v"),
    )
    rc = rdm.cursor()
    traced = trace_cursor.TracingCursor.of_cursor(rc.clone(), verbose=verbose)

    try:
        print(rc.doc_prefix())
        print(rc.doc_suffix())
        yield (rc, traced)
    finally:
        rc.dispose()
        traced.dispose()
        rdm.quit()


def same[T](fn: Callable[[RocqCursor], T], verbose: bool) -> None:
    with build_both(verbose) as (rc, traced):
        result = fn(rc)
        traced_result = fn(traced)
        assert type(result) is type(traced_result)
        if isinstance(result, RocqCursor.CommandData):
            assert isinstance(traced_result, RocqCursor.CommandData)
            assert result.proof_state == traced_result.proof_state
        elif isinstance(result, RocqCursor.Err):
            assert isinstance(traced_result, RocqCursor.Err)
            assert result.data == traced_result.data
        else:
            assert result == traced_result


_methods = [
    "insert_command",
    "query",
    "query_text_all",
    "query_json_all",
]


@pytest.mark.parametrize("verbose", [True, False], ids=[True, False])
@pytest.mark.parametrize(
    "method",
    _methods,
    ids=_methods,
)
def test_insert_command(verbose: bool, method: str) -> None:
    same(lambda rc: getattr(rc, method)("About nat."), verbose)


@pytest.mark.parametrize("verbose", [True, False], ids=[True, False])
@pytest.mark.parametrize(
    "method",
    ["query_json", "query_text"],
    ids=["query_json", "query_text"],
)
def test_with_index(verbose: bool, method: str) -> None:
    same(lambda rc: getattr(rc, method)("About nat.", index=0), verbose)


# @pytest.mark.parametrize("verbose", [True, False], ids=[True, False])
# def test_query(verbose: bool) -> None:
#     same(lambda rc: rc.query("About nat."), verbose)


# @pytest.mark.parametrize("verbose", [True, False], ids=[True, False])
# def test_query_text_all(verbose: bool) -> None:
#     same(lambda rc: rc.query_text_all("About nat."), verbose)


@pytest.mark.parametrize("verbose", [True, False], ids=[True, False])
def test_run_step(verbose: bool) -> None:
    same(lambda rc: rc.run_step(), verbose)
