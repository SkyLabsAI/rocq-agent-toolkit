from pathlib import Path

import pytest
from rocq_doc_manager import RocqDocManager
from rocq_doc_manager.locator import (
    CommentMarkerLocator,
    FirstAdmit,
    FirstLemma,
    Locator,
    LocatorParser,
)
from rocq_doc_manager.rocq_cursor import RocqCursor

TEST_CASES: dict[str, Locator] = {
    "Lemma:foo": FirstLemma("foo", "Lemma", 0),
    "Lemma:foo(22)": FirstLemma("foo", "Lemma", 22),
    "Theorem:foo": FirstLemma("foo", "Theorem", 0),
    "Theorem:foo(0)": FirstLemma("foo", "Theorem", 0),
    "Theorem:foo(1)": FirstLemma("foo", "Theorem", 1),
    "comment_marker:hello": CommentMarkerLocator("hello"),
    "comment_marker(1):hello": CommentMarkerLocator("hello", 1),
    "comment_marker(2):work": CommentMarkerLocator("work", 2),
    "comment_marker(77):work ok": CommentMarkerLocator("work ok", 77),
    "admit": FirstAdmit(0),
    "admit(33)": FirstAdmit(33),
}


@pytest.mark.parametrize("input, output", TEST_CASES.items(), ids=TEST_CASES.keys())
def test_comment_marker_test(input: str, output: Locator) -> None:
    assert LocatorParser.parse(input) == output


def check(rc: RocqCursor, loc: str, expected: int, next: bool = False) -> None:
    assert LocatorParser.parse(loc)(rc, next=next)
    assert rc.cursor_index() == expected, f"{loc}"


def test_find_admit() -> None:
    p = Path(__file__).parent / "locator_test.v"
    with RocqDocManager([], str(p)).sess(load_file=True) as rdm:
        rc = rdm.cursor()
        check(rc, "admit", 4)
        check(rc, "admit(1)", 12)
        check(rc, "admit", 4, next=False)
        check(rc, "admit(1)", 12, next=False)
        check(rc, "admit", 4, next=False)


def test_find_lemma() -> None:
    p = Path(__file__).parent / "locator_test.v"
    with RocqDocManager([], str(p)).sess(load_file=True) as rdm:
        rc = rdm.cursor()
        rc.go_to(0)
        check(rc, "Lemma:foo", 4)
        check(rc, "Lemma:foo(1)", 42, next=True)
        rc.go_to(0)
        check(rc, "Lemma:foo(1)", 22, next=True)
        check(rc, "Lemma:foo", 4, next=False)
        check(rc, "Lemma:foo(2)", 42, next=False)


def test_find_theorem() -> None:
    p = Path(__file__).parent / "locator_test.v"
    with RocqDocManager([], str(p)).sess(load_file=True) as rdm:
        rc = rdm.cursor()
        rc.go_to(0)
        check(rc, "Theorem:bar", 12)
        check(rc, "Theorem:bar(1)", 30)

        check(rc, "Theorem:bar", 12, next=False)
        check(rc, "Theorem:bar(1)", 30, next=False)
        check(rc, "Theorem:bar(2)", 50, next=False)
        check(rc, "Theorem:bar(1)", 30, next=False)
