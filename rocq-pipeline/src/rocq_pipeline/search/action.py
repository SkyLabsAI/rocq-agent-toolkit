from __future__ import annotations

import inspect
from collections.abc import Callable
from typing import Annotated, Any, TypeVar, override

from provenance_toolkit import Provenance

T_co = TypeVar("T_co", covariant=True)


class Action[T_co](Provenance.Full):
    """
    An `Action` represents a (potential) action in a Markov Decision Process (MDP).

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


class ActionWrapper[T_co](Action[T_co]):
    _base: Annotated[Action[T_co], Provenance.Reflect.Field]
    _fn: Annotated[
        Callable[[T_co], None], Provenance.Reflect.Field(transform=inspect.getsource)
    ]

    def __init__(self, base: Action[T_co], fn: Callable[[T_co], None]) -> None:
        self._fn = fn
        self._base = base

    def interact(self, state: T_co) -> T_co:
        self._fn(state)
        return self._base.interact(state)


class EmptyAction[T](Action[T]):
        """An action that does nothing and returns the input state."""

        @override
        def interact(self, state: T) -> T:
                return state

class ConditionalAction[T](Action[T]):
    """Execute one of two actions based on a test action."""

    _condition: Annotated[Action[T], Provenance.Reflect.Field]
    _then_action: Annotated[Action[T], Provenance.Reflect.Field]
    _else_action: Annotated[Action[T], Provenance.Reflect.Field]

    def __init__(
        self,
        condition: Action[T],
        then_action: Action[T],
        else_action: Action[T] = EmptyAction(),
    ) -> None:
        self._condition = condition
        self._then_action = then_action
        self._else_action = else_action

    @override
    def interact(self, state: T) -> T:
        try:
            self._condition.interact(state)
            return self._then_action.interact(state)
        except Action.Failed:
            return self._else_action.interact(state)

class ComposeAction[T](Action[T]):
    """Sequentially compose multiple actions into a single action."""

    _actions: Annotated[list[Action[T]], Provenance.Reflect.Field]

    def __init__(self, actions: list[Action[T]]) -> None:
        self._actions = actions

    @override
    def interact(self, state: T) -> T:
        for action in self._actions:
            state = action.interact(state)
        return state


class LoggingAction[T_co](Action[T_co]):
    """
    An action that logs itself when it is invoked.
    """

    _base: Annotated[Action[T_co], Provenance.Reflect.Field]
    _fn: Annotated[
        Callable[[T_co], None], Provenance.Reflect.Field(transform=inspect.getsource)
    ]

    def __init__(self, base: Action[T_co], fn: Callable[[T_co], None]) -> None:
        self._fn = fn
        self._base = base

    @override
    def interact(self, state: T_co) -> T_co:
        self._fn(state)
        return self._base.interact(state)


class MapAction[T_co, U](Action[T_co]):
    """
    Transport an action to another state type.

    Note that this is *invariant*.
    """

    _base: Annotated[Action[U], Provenance.Reflect.Field]
    _into: Annotated[Callable[[T_co], U], Provenance.Reflect.Field]
    _outof: Annotated[Callable[[U], T_co], Provenance.Reflect.Field]

    def __init__(
        self, base: Action[U], into: Callable[[T_co], U], outof: Callable[[U], T_co]
    ) -> None:
        self._base = base
        self._into = into
        self._outof = outof

    @override
    def interact(self, state: T_co) -> T_co:
        return self._outof(self._base.interact(self._into(state)))
