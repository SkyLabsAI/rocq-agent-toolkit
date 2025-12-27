from __future__ import annotations

from abc import abstractmethod
from collections.abc import Callable
from typing import TypeVar

T_co = TypeVar("T_co", covariant=True)


class Action[T_co]:
    """
    An `Action` represents a (potential) action in an MDP.

    They support failure in order to support instances
    where no action exists. Mathematically, failed actions
    could be modeled by enriching the MDP with a unique
    failure state, but explicitly communicating this
    avoids the need to modify the MDP.
    """

    class Failed(Exception):
        pass

    @abstractmethod
    def interact(self, state: T_co) -> T_co:
        """
        Returns the post state after the action.

        Raises `Action.Failed` if the action fails.
        """
        raise Action.Failed()

    def key(self) -> str:
        """Stable key for deduplication/repetition checks."""
        return f"{type(self).__name__}:{id(self)}"


class RetryAction[T](Action[T]):
    """
    Action wrapper that retries with correction on failure.

    This allows for self-correction loops where a failed action can be
    corrected and retried up to max_retries times. Generic over any state type.
    """

    def __init__(
        self,
        candidate: str,
        state_desc: str,
        corrector: Callable[[str, str, str], str | None] | None,
        to_action: Callable[[str], Action[T]],
        max_retries: int = 3,
    ) -> None:
        """
        Args:
            candidate: Initial candidate string to try
            state_desc: State description for correction context
            corrector: Function (state_desc, candidate, error) -> corrected_candidate | None
            to_action: Factory to create Action from candidate string
            max_retries: Maximum number of correction attempts
        """
        self._candidate = candidate
        self._state_desc = state_desc
        self._corrector = corrector
        self._to_action = to_action
        self._max_retries = max_retries
        self._final_candidate: str | None = None

    def interact(self, state: T) -> T:
        candidate = self._candidate
        last_error: str = ""

        for attempt in range(self._max_retries + 1):
            if attempt > 0 and self._corrector:
                corrected = self._corrector(self._state_desc, candidate, last_error)
                if corrected is None:
                    raise Action.Failed()
                candidate = corrected

            action = self._to_action(candidate)
            try:
                result = action.interact(state)
                self._final_candidate = candidate
                return result
            except Action.Failed:
                last_error = f"Candidate '{candidate}' failed"
                continue

        raise Action.Failed()

    def key(self) -> str:
        # Dedup by original candidate (corrections are internal)
        return self._candidate.strip()
