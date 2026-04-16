"""Tests for feedback span selection."""

from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_session.feedback import select_feedback_messages


def _cmd(text: str, offset: int) -> rdm_api.PrefixItem:
    return rdm_api.PrefixItem(text=text, offset=offset, kind="command", data=None)


def _blank(text: str, offset: int) -> rdm_api.PrefixItem:
    return rdm_api.PrefixItem(text=text, offset=offset, kind="blanks", data=None)


def test_selects_command_span() -> None:
    fb = rdm_api.FeedbackMessage(
        text="hello",
        quickfix=[],
        loc=None,
        level="info",
    )
    prefix = [_blank("\n", 0), _cmd("Check nat.", 1)]
    by_off: dict[int, list[rdm_api.FeedbackMessage]] = {1: [fb]}
    out = select_feedback_messages(prefix, 5, by_off)
    assert len(out) == 1
    assert out[0].text == "hello"


def test_blank_gap_returns_empty() -> None:
    prefix = [_blank("\n\n", 0), _cmd("Check nat.", 2)]
    by_off: dict[int, list[rdm_api.FeedbackMessage]] = {2: []}
    # Target in first blank only
    out = select_feedback_messages(prefix, 1, by_off)
    assert out == []
