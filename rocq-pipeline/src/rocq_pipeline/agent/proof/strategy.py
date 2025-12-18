from __future__ import annotations

import heapq
from abc import ABC, abstractmethod
from collections.abc import Generator
from typing import override

from rocq_doc_manager import RocqCursor


class Action[T]:
    @abstractmethod
    def interact(self, rc: T) -> bool:
        """
        Interact with the cursor and leave it in the new state.

        Returns `True` if the interaction was successful
        """
        return False


class RocqTacticAction(Action[RocqCursor]):
    def __init__(self, tactic: str) -> None:
        self._tactic = tactic

    @override
    def interact(self, rc: RocqCursor) -> bool:
        response = self.run_tactic(rc, self._tactic)
        return not issubclass(type(response), RocqCursor.Err)

    def run_tactic(
        self, rc: RocqCursor, tactic: str
    ) -> RocqCursor.CommandData | RocqCursor.Err[RocqCursor.CommandError]:
        return rc.insert_command(tactic)


class Strategy[T](ABC):
    """
    A `Strategy` proposes actions to take
    """

    # TODO: make [Rollout] into a class
    type Rollout[U] = Generator[tuple[float, Action[U]]]

    @abstractmethod
    def rollout(self, cursor: T, max_rollout: int | None = None) -> Rollout[T]:
        """
        Given the goal `G`, generates `(Pr,A)` such that:
        - `Pr` is the probability that `A` is (the next/a necessary) step in an
            efficient proof of `G`

        Notes:
        - If a strategy does not apply, it should produce an empty generator.
        - The returned generator **must** return results with decreasing
            probability since clients will generally not ask for a new `Action`
            unless the previous one did not work.
        """
        pass


def empty_Rollout[T]() -> Strategy.Rollout[T]:
    yield from ()


class CompositeStrategy[T](Strategy[T]):
    """A (fair) combination of strategies"""

    def __init__(self, children: list[Strategy[T]]) -> None:
        self._children: list[Strategy[T]] = children

    @override
    def rollout(self, rdm: T, max_rollout: int | None = None) -> Strategy.Rollout[T]:
        def combine() -> Strategy.Rollout[T]:
            queue: list[tuple[float, int, Action[T], Strategy.Rollout[T]]] = []
            for i, strat in enumerate(self._children):
                gen = strat.rollout(rdm, max_rollout=max_rollout)
                try:
                    pr, act = next(gen)
                except StopIteration:
                    continue
                heapq.heappush(queue, (pr, i, act, gen))

            while True:
                try:
                    (pr, i, act, gen) = heapq.heappop(queue)
                except IndexError:
                    return
                yield (pr, act)
                try:
                    pr, act = next(gen)
                except StopIteration:
                    continue
                heapq.heappush(queue, (pr, i, act, gen))

        return combine()


class SafeTacticStrategy(Strategy[RocqCursor]):
    """A simple strategy that always returns a tactic."""

    def __init__(self, tactic: str, prob: float = 1.0) -> None:
        self._tactic: str = tactic
        self._prob: float = prob

    @override
    def rollout(
        self, rdm: RocqCursor, max_rollout: int | None = None
    ) -> Strategy.Rollout:
        return (
            (prob, RocqTacticAction(f"progress {tac}"))
            for prob, tac in [(self._prob, self._tactic)]
        )


class CutAssertStrategy(Strategy[RocqCursor]):
    """A simple strategy that cuts a Rocq lemma.
    The success probability 1.0 is not necessarily appropriate."""

    def __init__(self, name: str, lemma: str, prob: float = 1.0) -> None:
        self._name: str = name
        self._lemma: str = lemma
        self._prob: float = prob

    @override
    def rollout(
        self, rdm: RocqCursor, max_rollout: int | None = None
    ) -> Strategy.Rollout:
        name: str | RocqCursor.Err[None] = rdm.fresh_ident(self._name)
        if isinstance(name, RocqCursor.Err):
            return empty_Rollout()

        # For now, it is important that we fail if this fact is already known,
        # otherwise we risk looping here
        tac: str = f"assert ({self._lemma}) as {name}; [ assert_fails tauto | ]"

        return ((prob, RocqTacticAction(t)) for prob, t in [(self._prob, tac)])


class FailStrategy[T](Strategy[T]):
    """A simple strategy that fails."""

    @override
    def rollout(self, rdm: T, max_rollout: int | None = None) -> Strategy.Rollout[T]:
        return empty_Rollout()


class FirstTacticStrategy(Strategy[RocqCursor]):
    """A simple strategy that tries each of the given tactics with their given probabilities."""

    def __init__(self, tactics: list[tuple[float, str | Action]]) -> None:
        def mk(x: str | Action) -> Action:
            if isinstance(x, Action):
                return x
            return RocqTacticAction(x)

        self._tactics: list[tuple[float, Action]] = [
            (prob, mk(tac)) for prob, tac in sorted(tactics, reverse=True)
        ]

    @override
    def rollout(
        self, rdm: RocqCursor, max_rollout: int | None = None
    ) -> Strategy.Rollout:
        return ((prob, tac) for prob, tac in self._tactics)


class GuardStrategy[T](FailStrategy[T], ABC):
    """Guard the execution of a strategy.
    If [check] returns [None], then this strategy acts like the [FailStrategy] otherwise
    it does [rollout_with]
    """

    @abstractmethod
    def check(self, rdm: T) -> T | None: ...

    @abstractmethod
    def rollout_with(
        self, val: T, rdm: T, max_rollout: int | None = None
    ) -> Strategy.Rollout[T]: ...

    @override
    def rollout(self, rdm: T, max_rollout: int | None = None) -> Strategy.Rollout[T]:
        val = self.check(rdm)
        if val is None:
            return super().rollout(rdm, max_rollout)
        return self.rollout_with(val, rdm, max_rollout)
