"""Shared test fixtures and mocks for rocq search tests."""

from unittest.mock import patch

import pytest
from rocq_doc_manager import rocq_doc_manager_api as rdm_api


class MockRocqCursor:
    """Mock RocqCursor for testing without actual Rocq session."""

    def __init__(self, goal: str = "∀ n, n + 0 = n") -> None:
        self._goal = goal
        self._commands: list[str] = []
        self._fail_commands: dict[str, str] = {}  # command -> error message

    def current_goal(self) -> str | None:
        return self._goal

    def insert_command(
        self, text: str, blanks: str | None = "\n", safe: bool = True
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        del blanks, safe
        self._commands.append(text)
        if text in self._fail_commands:
            return rdm_api.Err(
                message=self._fail_commands[text],
                data=rdm_api.CommandError(),
            )
        return rdm_api.CommandData()

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
