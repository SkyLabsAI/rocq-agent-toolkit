"""Unit tests for RocqTacticAction and RocqRetryAction."""

from collections.abc import Awaitable, Callable
from typing import cast
from unittest.mock import AsyncMock

import pytest
from rocq_doc_manager import RocqCursor
from rocq_pipeline.search.action import Action
from rocq_pipeline.search.rocq.actions import RocqRetryCommandAction, RocqTacticAction

from .conftest import MockRocqCursor

pytestmark = pytest.mark.asyncio


class TestRocqTacticAction:
    """Tests for RocqTacticAction."""

    async def test_successful_tactic(self) -> None:
        """Action succeeds when tactic succeeds."""
        cursor = MockRocqCursor()
        action = RocqTacticAction("auto")

        result = await action.interact(cast(RocqCursor, cursor))

        assert result is cursor
        assert cursor._commands == ["auto."]

    async def test_failed_tactic_raises_with_message(self) -> None:
        """Action.Failed includes error message from Rocq."""
        cursor = MockRocqCursor()
        cursor.set_failure("bad_tactic.", "Unknown tactic: bad_tactic")
        action = RocqTacticAction("bad_tactic")

        with pytest.raises(Action.Failed) as exc_info:
            await action.interact(cast(RocqCursor, cursor))

        assert exc_info.value.message == "Unknown tactic: bad_tactic"

    async def test_key_returns_tactic(self) -> None:
        """key() returns the tactic string for deduplication."""
        action = RocqTacticAction("reflexivity")
        assert action.key() == "reflexivity"

    async def test_normalize_whitespace_and_periods(self) -> None:
        """Tactics with whitespace and trailing periods are normalized."""
        # Test whitespace normalization
        action1 = RocqTacticAction("  reflexivity  ")
        assert action1.key() == "reflexivity"

        # Test period stripping
        action2 = RocqTacticAction("apply H.")
        assert action2.key() == "apply H"

        # Test both together
        action3 = RocqTacticAction("  auto.  ")
        assert action3.key() == "auto"


class TestRocqRetryAction:
    """Tests for RocqRetryAction."""

    @staticmethod
    def fixed_rectifier(
        return_value: str, trace: list[tuple[RocqCursor, str, str]]
    ) -> Callable[[RocqCursor, str, str], Awaitable[str | None]]:
        async def fn(rc: RocqCursor, tactic: str, error: str) -> str | None:
            nonlocal trace
            trace.append((rc, tactic, error))
            return "good."

        return fn

    async def test_succeeds_on_first_attempt(self) -> None:
        """No rectification needed when first attempt succeeds."""
        cursor = MockRocqCursor()
        rectifier = AsyncMock(return_value="fixed.")
        action = RocqRetryCommandAction("auto.", rectifier=rectifier, max_retries=3)

        result = await action.interact(cast(RocqCursor, cursor))

        assert result is cursor
        assert cursor._commands == ["auto."]
        rectifier.assert_not_called()

    async def test_rectifies_on_failure(self) -> None:
        """Rectifier is called with cursor, tactic, and error on failure."""
        cursor = MockRocqCursor(goal="my test goal")
        cursor.set_failure("bad.", "Syntax error")

        # Rectifier returns fixed tactic
        rectifier = AsyncMock(return_value="good.")

        action = RocqRetryCommandAction("bad.", rectifier=rectifier, max_retries=3)
        result = await action.interact(cast(RocqCursor, cursor))

        assert result is cursor
        assert cursor._commands == ["bad.", "good."]
        rectifier.assert_awaited_with(cast(RocqCursor, cursor), "bad.", "Syntax error")

    async def test_multiple_rectification_attempts(self) -> None:
        """Rectifier is called multiple times if needed."""
        cursor = MockRocqCursor(goal="goal")
        cursor.set_failure("try1.", "Error 1")
        cursor.set_failure("try2.", "Error 2")

        # First rectification also fails, second succeeds
        rectifier = AsyncMock(side_effect=["try2.", "try3."])

        action = RocqRetryCommandAction("try1.", rectifier=rectifier, max_retries=3)
        result = await action.interact(cast(RocqCursor, cursor))

        assert result is cursor
        assert cursor._commands == ["try1.", "try2.", "try3."]
        assert rectifier.await_count == 2

    async def test_fails_after_max_retries(self) -> None:
        """Raises Action.Failed after exhausting retries."""
        cursor = MockRocqCursor()
        cursor.set_failure("always_fails.", "Specific Rocq Error")

        rectifier = AsyncMock(
            return_value="always_fails."
        )  # Keeps returning same bad tactic

        action = RocqRetryCommandAction(
            "always_fails.", rectifier=rectifier, max_retries=2
        )

        with pytest.raises(Action.Failed) as exc_info:
            await action.interact(cast(RocqCursor, cursor))

        assert "Max retries (2) exceeded" in exc_info.value.message
        assert "Specific Rocq Error" in exc_info.value.message
        # Original + 2 retries = 3 attempts
        assert len(cursor._commands) == 3
        # Ensure details contains the Rocq error
        assert exc_info.value.details.message == "Specific Rocq Error"

    async def test_fails_when_rectifier_returns_none(self) -> None:
        """Raises Action.Failed if rectifier gives up."""
        cursor = MockRocqCursor()
        cursor.set_failure("bad.", "Original Error")

        rectifier = AsyncMock(return_value=None)  # Gives up

        action = RocqRetryCommandAction("bad.", rectifier=rectifier, max_retries=3)

        with pytest.raises(Action.Failed) as exc_info:
            await action.interact(cast(RocqCursor, cursor))

        assert "Could not rectify" in exc_info.value.message
        assert "Original Error" in exc_info.value.message
        assert exc_info.value.details.message == "Original Error"

    async def test_no_rectifier_fails_immediately(self) -> None:
        """Without rectifier, fails on first attempt and does NOT retry."""
        cursor = MockRocqCursor()
        cursor.set_failure("bad.", "Error")

        action = RocqRetryCommandAction("bad.", rectifier=None, max_retries=3)

        with pytest.raises(Action.Failed):
            await action.interact(cast(RocqCursor, cursor))

        # Without rectifier, it should only try once
        assert len(cursor._commands) == 1

    async def test_final_tactic_reset_on_failure(self) -> None:
        """final_tactic is reset to None if a subsequent interact() fails."""
        cursor = MockRocqCursor()
        cursor.set_failure("bad.", "Error")

        # 1. First run succeeds
        action = RocqRetryCommandAction("good.", rectifier=None)
        await action.interact(cast(RocqCursor, cursor))
        assert action.final_command == "good."

        # 2. Second run with same action instance fails
        action = RocqRetryCommandAction("bad.", rectifier=None)
        with pytest.raises(Action.Failed):
            await action.interact(cast(RocqCursor, cursor))

        # final_tactic should now be None, not "good."
        assert action.final_command is None

    async def test_final_tactic_none_before_interact(self) -> None:
        """final_tactic is None before interact() is called."""
        action = RocqRetryCommandAction("tactic", rectifier=None, max_retries=1)
        assert action.final_command is None

    async def test_final_tactic_equals_original_on_success(self) -> None:
        """final_tactic equals original when no rectification needed."""
        cursor = MockRocqCursor()
        action = RocqRetryCommandAction("auto.", rectifier=None, max_retries=1)

        await action.interact(cast(RocqCursor, cursor))

        assert action.final_command == "auto."
        assert action.key() == "auto."  # Same as final

    async def test_final_tactic_differs_after_rectification(self) -> None:
        """final_tactic differs from key() after rectification."""
        cursor = MockRocqCursor()
        cursor.set_failure("bad.", "Error")
        rectifier = AsyncMock(return_value="good.")

        action = RocqRetryCommandAction("bad.", rectifier=rectifier, max_retries=3)
        await action.interact(cast(RocqCursor, cursor))

        assert action.key() == "bad."  # Original for dedup
        assert action.final_command == "good."  # What actually ran
