"""Shared test fixtures and mocks for rocq search tests."""

from typing import Any
from unittest.mock import MagicMock, patch

import pytest
from rocq_doc_manager import rocq_doc_manager_api as api


class MockRocqCursor:
    """Mock RocqCursor for testing without actual Rocq session."""

    def __init__(self, goal: str = "∀ n, n + 0 = n") -> None:
        self._goal = goal
        self._commands: list[str] = []
        self._fail_commands: dict[str, str] = {}  # command -> error message

    def current_goal(self) -> str | None:
        return self._goal

    def insert_command(self, cmd: str) -> Any:
        self._commands.append(cmd)
        if cmd in self._fail_commands:
            return api.Err(data=None, message=self._fail_commands[cmd])
        return MagicMock()  # Success response

    def set_failure(self, command: str, error: str) -> None:
        """Configure a command to fail with given error."""
        self._fail_commands[command] = error

    def clear_failure(self, command: str) -> None:
        """Clear failure for a command."""
        self._fail_commands.pop(command, None)


@pytest.fixture(autouse=True)
def patch_rocq_cursor():
    """Patch RocqCursor in the actions module for all tests in this directory."""
    with patch("rocq_pipeline.search.rocq.actions.RocqCursor", MockRocqCursor):
        yield
