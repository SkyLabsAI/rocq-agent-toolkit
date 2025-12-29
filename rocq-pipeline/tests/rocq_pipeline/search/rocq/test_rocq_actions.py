"""Unit tests for RocqTacticAction and RocqRetryAction."""

from unittest.mock import MagicMock

import pytest
from rocq_pipeline.search.action import Action
from rocq_pipeline.search.rocq.actions import RocqRetryAction, RocqTacticAction

from .conftest import MockRocqCursor


class TestRocqTacticAction:
    """Tests for RocqTacticAction."""

    def test_successful_tactic(self) -> None:
        """Action succeeds when tactic succeeds."""
        cursor = MockRocqCursor()
        action = RocqTacticAction("auto.")

        result = action.interact(cursor)

        assert result is cursor
        assert cursor._commands == ["auto."]

    def test_failed_tactic_raises_with_message(self) -> None:
        """Action.Failed includes error message from Rocq."""
        cursor = MockRocqCursor()
        cursor.set_failure("bad_tactic", "Unknown tactic: bad_tactic")
        action = RocqTacticAction("bad_tactic")

        with pytest.raises(Action.Failed) as exc_info:
            action.interact(cursor)

        assert exc_info.value.message == "Unknown tactic: bad_tactic"

    def test_key_returns_tactic(self) -> None:
        """key() returns the tactic string for deduplication."""
        action = RocqTacticAction("  reflexivity.  ")
        assert action.key() == "reflexivity."


class TestRocqRetryAction:
    """Tests for RocqRetryAction."""

    def test_succeeds_on_first_attempt(self) -> None:
        """No rectification needed when first attempt succeeds."""
        cursor = MockRocqCursor()
        rectifier = MagicMock(return_value="fixed.")
        action = RocqRetryAction("auto.", rectifier=rectifier, max_retries=3)

        result = action.interact(cursor)

        assert result is cursor
        assert cursor._commands == ["auto."]
        rectifier.assert_not_called()

    def test_rectifies_on_failure(self) -> None:
        """Rectifier is called with goal, tactic, and error on failure."""
        cursor = MockRocqCursor(goal="my test goal")
        cursor.set_failure("bad.", "Syntax error")

        # Rectifier returns fixed tactic
        rectifier = MagicMock(return_value="good.")

        action = RocqRetryAction("bad.", rectifier=rectifier, max_retries=3)
        result = action.interact(cursor)

        assert result is cursor
        assert cursor._commands == ["bad.", "good."]
        rectifier.assert_called_once_with("my test goal", "bad.", "Syntax error")

    def test_multiple_rectification_attempts(self) -> None:
        """Rectifier is called multiple times if needed."""
        cursor = MockRocqCursor(goal="goal")
        cursor.set_failure("try1", "Error 1")
        cursor.set_failure("try2", "Error 2")

        # First rectification also fails, second succeeds
        rectifier = MagicMock(side_effect=["try2", "try3"])

        action = RocqRetryAction("try1", rectifier=rectifier, max_retries=3)
        result = action.interact(cursor)

        assert result is cursor
        assert cursor._commands == ["try1", "try2", "try3"]
        assert rectifier.call_count == 2

    def test_fails_after_max_retries(self) -> None:
        """Raises Action.Failed after exhausting retries."""
        cursor = MockRocqCursor()
        cursor.set_failure("always_fails", "Specific Rocq Error")

        rectifier = MagicMock(
            return_value="always_fails"
        )  # Keeps returning same bad tactic

        action = RocqRetryAction("always_fails", rectifier=rectifier, max_retries=2)

        with pytest.raises(Action.Failed) as exc_info:
            action.interact(cursor)

        assert "Max retries (2) exceeded" in exc_info.value.message
        assert "Specific Rocq Error" in exc_info.value.message
        # Original + 2 retries = 3 attempts
        assert len(cursor._commands) == 3
        # Ensure details contains the Rocq error
        assert exc_info.value.details.message == "Specific Rocq Error"

    def test_fails_when_rectifier_returns_none(self) -> None:
        """Raises Action.Failed if rectifier gives up."""
        cursor = MockRocqCursor()
        cursor.set_failure("bad.", "Original Error")

        rectifier = MagicMock(return_value=None)  # Gives up

        action = RocqRetryAction("bad.", rectifier=rectifier, max_retries=3)

        with pytest.raises(Action.Failed) as exc_info:
            action.interact(cursor)

        assert "Could not rectify" in exc_info.value.message
        assert "Original Error" in exc_info.value.message
        assert exc_info.value.details.message == "Original Error"

    def test_no_rectifier_fails_immediately(self) -> None:
        """Without rectifier, fails on first attempt and does NOT retry."""
        cursor = MockRocqCursor()
        cursor.set_failure("bad.", "Error")

        action = RocqRetryAction("bad.", rectifier=None, max_retries=3)

        with pytest.raises(Action.Failed):
            action.interact(cursor)

        # Without rectifier, it should only try once
        assert len(cursor._commands) == 1

    def test_final_tactic_reset_on_failure(self) -> None:
        """final_tactic is reset to None if a subsequent interact() fails."""
        cursor = MockRocqCursor()
        cursor.set_failure("bad.", "Error")

        # 1. First run succeeds
        action = RocqRetryAction("good.", rectifier=None)
        action.interact(cursor)
        assert action.final_tactic == "good."

        # 2. Second run with same action instance fails
        action._tactic = "bad."
        with pytest.raises(Action.Failed):
            action.interact(cursor)

        # final_tactic should now be None, not "good."
        assert action.final_tactic is None

    def test_final_tactic_none_before_interact(self) -> None:
        """final_tactic is None before interact() is called."""
        action = RocqRetryAction("tactic.", rectifier=None, max_retries=1)
        assert action.final_tactic is None

    def test_final_tactic_equals_original_on_success(self) -> None:
        """final_tactic equals original when no rectification needed."""
        cursor = MockRocqCursor()
        action = RocqRetryAction("auto.", rectifier=None, max_retries=1)

        action.interact(cursor)

        assert action.final_tactic == "auto."
        assert action.key() == "auto."  # Same as final

    def test_final_tactic_differs_after_rectification(self) -> None:
        """final_tactic differs from key() after rectification."""
        cursor = MockRocqCursor()
        cursor.set_failure("bad.", "Error")
        rectifier = MagicMock(return_value="good.")

        action = RocqRetryAction("bad.", rectifier=rectifier, max_retries=3)
        action.interact(cursor)

        assert action.key() == "bad."  # Original for dedup
        assert action.final_tactic == "good."  # What actually ran
