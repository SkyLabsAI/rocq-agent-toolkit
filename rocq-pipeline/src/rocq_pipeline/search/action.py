from __future__ import annotations

from abc import abstractmethod
from typing import Any, TypeVar

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
