from __future__ import annotations

from abc import abstractmethod


class Action[T]:
    """
    An `Action` represents a (potential) action in an MDP.

    They support failure in order to support instances
    where no action exists. Mathematically, failed actions
    could be modeled by enriching the MDP with a unique
    failure state, but explicitly communicating this
    avoids the need to modify the MDP.
    """

    @abstractmethod
    def interact(self, rc: T) -> bool:
        return False
