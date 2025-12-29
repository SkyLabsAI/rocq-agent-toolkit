from __future__ import annotations

from collections.abc import Callable
from typing import Any, TypeVar, override

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
        """Action failure with optional error details."""

        def __init__(self, message: str = "", details: Any = None) -> None:
            self.message = message
            self.details = details
            super().__init__(message)

    def interact(self, state: T_co) -> T_co:
        """
        Returns the post state after the action.

        Raises `Action.Failed` if the action fails.
        """
        raise Action.Failed()

    def key(self) -> str:
        """Stable key for deduplication/repetition checks."""
        return f"{type(self).__name__}:{id(self)}"


class LoggingAction[T_co](Action[T_co]):
    """
    An action that logs itself when it is invoked.
    """

    def __init__(self, base: Action[T_co], record: Callable[[T_co], None]) -> None:
        self._record = record
        self._base = base

    @override
    def interact(self, state: T_co) -> T_co:
        self._record(state)
        return self._base.interact(state)
