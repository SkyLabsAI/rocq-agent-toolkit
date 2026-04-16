"""Tests for the per-session feedback cache in ``rocq_session.feedback``."""

from __future__ import annotations

import asyncio
from dataclasses import dataclass, field
from typing import Literal, cast

import pytest
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_session.feedback import FeedbackCache, feedback_at_byte

StepResult = rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError] | None
PrefixKind = Literal["blanks", "command", "ghost"]


def _vernac() -> rdm_api.VernacData:
    return rdm_api.VernacData(kind="Noop")


def _cmd_data(messages: list[rdm_api.FeedbackMessage]) -> rdm_api.CommandData:
    return rdm_api.CommandData(synterp_ast=_vernac(), feedback_messages=messages)


def _fb(text: str) -> rdm_api.FeedbackMessage:
    return rdm_api.FeedbackMessage(text=text, quickfix=[], loc=None, level="info")


def _pi(text: str, offset: int, kind: PrefixKind) -> rdm_api.PrefixItem:
    return rdm_api.PrefixItem(text=text, offset=offset, kind=kind, data=None)


@dataclass
class FakeStep:
    result: StepResult
    prefix_after: list[rdm_api.PrefixItem]


@dataclass
class FakeCursor:
    """Minimal cursor simulating a pre-scripted sequence of steps."""

    steps: list[FakeStep]
    step_index: int = 0
    step_calls: int = 0
    go_to_calls: int = 0
    go_to_result: rdm_api.Err[rdm_api.CommandError | None] | None = field(default=None)

    async def go_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        self.go_to_calls += 1
        self.step_index = 0
        return self.go_to_result

    async def has_suffix(self) -> bool:
        return self.step_index < len(self.steps)

    async def run_step(self) -> StepResult:
        if self.step_index >= len(self.steps):
            raise AssertionError("run_step called past end of script")
        step = self.steps[self.step_index]
        self.step_index += 1
        self.step_calls += 1
        return step.result

    async def doc_prefix(self) -> list[rdm_api.PrefixItem]:
        if self.step_index == 0:
            return []
        return self.steps[self.step_index - 1].prefix_after


def _two_command_script() -> list[FakeStep]:
    # Document: "Check nat.\nCheck bool."
    #           01234567890 1 234567890123
    # cmd1: offset 0, text "Check nat.", byte_end 10, feedback "fb1"
    # blank: offset 10, text "\n"
    # cmd2: offset 11, text "Check bool.", byte_end 22, feedback "fb2"
    cmd1 = _pi("Check nat.", 0, "command")
    blank = _pi("\n", 10, "blanks")
    cmd2 = _pi("Check bool.", 11, "command")
    return [
        FakeStep(result=_cmd_data([_fb("fb1")]), prefix_after=[cmd1]),
        FakeStep(result=None, prefix_after=[cmd1, blank]),
        FakeStep(result=_cmd_data([_fb("fb2")]), prefix_after=[cmd1, blank, cmd2]),
    ]


@pytest.mark.asyncio
async def test_cache_hit_avoids_rerun() -> None:
    cursor = FakeCursor(_two_command_script())
    cache = FeedbackCache()
    lock = asyncio.Lock()

    first = await feedback_at_byte(cast(RocqCursor, cursor), 5, cache, lock)
    assert first["status"] == "ok"
    assert [m["text"] for m in first["feedback_messages"]] == ["fb1"]
    calls_after_first = cursor.step_calls

    second = await feedback_at_byte(cast(RocqCursor, cursor), 2, cache, lock)
    assert second == first
    assert cursor.step_calls == calls_after_first
    assert cursor.go_to_calls == 1


@pytest.mark.asyncio
async def test_cache_extends_on_later_request() -> None:
    cursor = FakeCursor(_two_command_script())
    cache = FeedbackCache()
    lock = asyncio.Lock()

    first = await feedback_at_byte(cast(RocqCursor, cursor), 5, cache, lock)
    steps_after_first = cursor.step_calls
    assert first["feedback_messages"][0]["text"] == "fb1"

    second = await feedback_at_byte(cast(RocqCursor, cursor), 15, cache, lock)
    assert second["status"] == "ok"
    assert [m["text"] for m in second["feedback_messages"]] == ["fb2"]
    assert cursor.step_calls > steps_after_first

    steps_after_second = cursor.step_calls
    third = await feedback_at_byte(cast(RocqCursor, cursor), 15, cache, lock)
    assert third == second
    assert cursor.step_calls == steps_after_second


@pytest.mark.asyncio
async def test_blank_region_returns_empty_and_caches() -> None:
    cursor = FakeCursor(_two_command_script())
    cache = FeedbackCache()
    lock = asyncio.Lock()

    result = await feedback_at_byte(cast(RocqCursor, cursor), 10, cache, lock)
    assert result["status"] == "ok"
    assert result["feedback_messages"] == []


@pytest.mark.asyncio
async def test_past_end_is_sticky() -> None:
    cursor = FakeCursor(_two_command_script())
    cache = FeedbackCache()
    lock = asyncio.Lock()

    past_end = await feedback_at_byte(cast(RocqCursor, cursor), 1000, cache, lock)
    assert past_end["status"] == "error"
    assert "end of the processed document" in past_end["message"]

    steps_after = cursor.step_calls
    again = await feedback_at_byte(cast(RocqCursor, cursor), 500, cache, lock)
    assert again == past_end
    assert cursor.step_calls == steps_after

    in_cache = await feedback_at_byte(cast(RocqCursor, cursor), 5, cache, lock)
    assert in_cache["status"] == "ok"
    assert [m["text"] for m in in_cache["feedback_messages"]] == ["fb1"]


@pytest.mark.asyncio
async def test_run_step_error_is_cached() -> None:
    cmd1 = _pi("Check nat.", 0, "command")
    err = rdm_api.Err[rdm_api.CommandError](
        "boom",
        rdm_api.CommandError(
            feedback_messages=[_fb("err_fb")],
            error_loc=None,
        ),
    )
    steps = [
        FakeStep(result=_cmd_data([_fb("fb1")]), prefix_after=[cmd1]),
        FakeStep(result=err, prefix_after=[cmd1]),
    ]
    cursor = FakeCursor(steps)
    cache = FeedbackCache()
    lock = asyncio.Lock()

    bad = await feedback_at_byte(cast(RocqCursor, cursor), 100, cache, lock)
    assert bad["status"] == "error"
    assert bad["message"] == "boom"
    assert [m["text"] for m in bad["feedback_messages"]] == ["err_fb"]

    steps_after = cursor.step_calls
    again = await feedback_at_byte(cast(RocqCursor, cursor), 200, cache, lock)
    assert again == bad
    assert cursor.step_calls == steps_after

    in_cache = await feedback_at_byte(cast(RocqCursor, cursor), 5, cache, lock)
    assert in_cache["status"] == "ok"
    assert [m["text"] for m in in_cache["feedback_messages"]] == ["fb1"]


@pytest.mark.asyncio
async def test_initialization_failure_is_sticky() -> None:
    cursor = FakeCursor(
        _two_command_script(),
        go_to_result=rdm_api.Err[rdm_api.CommandError | None]("nope", None),
    )
    cache = FeedbackCache()
    lock = asyncio.Lock()

    first = await feedback_at_byte(cast(RocqCursor, cursor), 0, cache, lock)
    assert first["status"] == "error"
    assert first["message"] == "nope"

    second = await feedback_at_byte(cast(RocqCursor, cursor), 20, cache, lock)
    assert second == first
    assert cursor.step_calls == 0
    assert cursor.go_to_calls == 1
