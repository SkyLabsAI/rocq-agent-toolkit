from pathlib import Path

import pytest
from rocq_doc_manager import RocqDocManager
from rocq_doc_manager.rocq_cursor import RocqCursor
from rocq_pipeline.locator import (
    FirstAdmit,
    FirstLemma,
    Locator,
    MarkerCommentLocator,
)

TEST_CASES: dict[str, Locator] = {
    "Lemma:foo": FirstLemma("foo", "Lemma", 0),
    "Lemma:foo(22)": FirstLemma("foo", "Lemma", 22),
    "Theorem:foo": FirstLemma("foo", "Theorem", 0),
    "Theorem:foo(0)": FirstLemma("foo", "Theorem", 0),
    "Theorem:foo(1)": FirstLemma("foo", "Theorem", 1),
    "comment_marker:hello": MarkerCommentLocator("hello"),
    "comment_marker(1):hello": MarkerCommentLocator("hello", 1),
    "comment_marker(2):work": MarkerCommentLocator("work", 2),
    "comment_marker(77):work ok": MarkerCommentLocator("work ok", 77),
    "admit": FirstAdmit(0),
    "admit(33)": FirstAdmit(33),
}


@pytest.mark.parametrize("input, output", TEST_CASES.items(), ids=TEST_CASES.keys())
def test_comment_marker_test(input: str, output: Locator) -> None:
    assert Locator.parse(input) == output


def test_find_admit() -> None:
    def check(rc: RocqCursor, loc: str, expected: int) -> None:
        assert Locator.parse(loc)(rc)
        assert rc.cursor_index() == expected, f"{loc}"

    p = Path(__file__).parent / "locator_test.v"
    with RocqDocManager([], str(p)).sess(load_file=True) as rdm:
        rc = rdm.cursor()
        rc.go_to(0)
        check(rc, "Lemma:foo", 4)
        check(rc, "Lemma:foo(1)", 42)
        rc.go_to(0)
        check(rc, "Theorem:bar", 12)
        check(rc, "Theorem:bar(1)", 50)
        rc.go_to(0)
        check(rc, "admit", 4)
        check(rc, "admit(1)", 12)
