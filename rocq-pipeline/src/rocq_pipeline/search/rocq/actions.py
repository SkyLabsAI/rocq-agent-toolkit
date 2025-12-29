from collections.abc import Callable
from typing import override

from rocq_doc_manager import RocqCursor

from ..action import Action


class RocqTacticAction(Action[RocqCursor]):
    """Execute a single Rocq tactic."""

    def __init__(self, tactic: str) -> None:
        self._tactic = tactic

    @override
    def interact(self, state: RocqCursor) -> RocqCursor:
        # TODO: the fact that cursors are not functional is quite annoying here.
        # It should be the caller that creates a new cursor, but in this case
        # we will basically always be returning our own cursor.
        # If cursors were functional, we would just be returning the latest
        # cursor here.
        response = self.run_tactic(state, self._tactic)
        if issubclass(type(response), RocqCursor.Err):
            # Preserve the actual Rocq error message
            raise Action.Failed(
                message=response.message,
                details=response,
            )
        return state

    def run_tactic(
        self, rc: RocqCursor, tactic: str
    ) -> RocqCursor.CommandData | RocqCursor.Err[RocqCursor.CommandError]:
        return rc.insert_command(tactic)

    @override
    def key(self) -> str:
        return self._tactic.strip()


class RocqRetryAction(RocqTacticAction):
    """
    Rocq tactic with LLM-based rectification on failure.

    Inherits tactic execution from RocqTacticAction and adds:
    - Goal extraction from cursor for rectification context
    - Real Rocq error message preservation
    - Retry loop with rectifier callback

    After interact() completes successfully, use `final_tactic` to get the
    tactic that actually succeeded (which may differ from the original if
    rectification occurred).
    """

    def __init__(
        self,
        tactic: str,
        rectifier: Callable[[str, str, str], str | None] | None,
        max_retries: int = 3,
    ) -> None:
        """
        Args:
            tactic: Initial tactic string to try
            rectifier: Function (goal, tactic, error) -> rectified_tactic | None
            max_retries: Maximum number of rectification attempts
        """
        super().__init__(tactic)
        self._rectifier = rectifier
        self._max_retries = max_retries
        self._final_tactic: str | None = None

    @property
    def final_tactic(self) -> str | None:
        """
        The tactic that actually succeeded (after any rectification).

        Returns None if interact() hasn't been called or failed.
        Use this for logging/tracing what actually ran.
        """
        return self._final_tactic

    @override
    def interact(self, state: RocqCursor) -> RocqCursor:
        self._final_tactic = None  # Reset stale state
        tactic = self._tactic
        last_error: str = ""
        last_response: RocqCursor.Err | None = None

        # If no rectifier is provided, we only try once to avoid repeating side effects
        max_attempts = (self._max_retries + 1) if self._rectifier else 1

        for attempt in range(max_attempts):
            if attempt > 0 and self._rectifier:
                # Extract goal from cursor for rectification context
                goal = self._extract_goal(state)
                # NOTE: the rectifier probably doesn't need the goal
                # but maybe a future implementation could use it for improved rectification
                rectified = self._rectifier(goal, tactic, last_error)
                if rectified is None:
                    raise Action.Failed(
                        message=f"Could not rectify after {attempt} attempts: {last_error}",
                        details=last_response,
                    )
                tactic = rectified

            # Use inherited run_tactic method
            response = self.run_tactic(state, tactic)

            if issubclass(type(response), RocqCursor.Err):
                # Preserve real Rocq error for next rectification attempt
                last_error = response.message
                last_response = response
                continue

            # Success! Store what actually worked
            self._final_tactic = tactic
            return state

        raise Action.Failed(
            message=(
                f"Max retries ({self._max_retries}) exceeded for '{self._tactic}'. "
                f"Last error: {last_error}"
            ),
            details=last_response,
        )

    def _extract_goal(self, state: RocqCursor) -> str:
        """Extract current goal from cursor for rectification context."""
        goal = state.current_goal()
        if goal is None or isinstance(goal, RocqCursor.Err):
            return ""
        return goal

    @override
    def key(self) -> str:
        """
        Returns the original tactic for deduplication and loop detection.

        We use the original (not rectified) tactic because:
        1. Deduplication: If the generator suggests "autoo." multiple times,
           we shouldn't retry it—it'll just rectify to the same thing.
        2. Loop detection: The repetition policy checks recent action keys
           to prevent cycles. Using original keys ensures we detect when
           the generator keeps suggesting the same broken tactic.

        For the tactic that actually succeeded, use `final_tactic` instead.
        """
        return self._tactic.strip()
