import heapq
from abc import ABC, abstractmethod
from collections.abc import Generator
from typing import override

from rocq_doc_manager import RocqDocManager

from rocq_pipeline.agent.base import TacticApplication


class Strategy(ABC):
    """
    A `Strategy` proposes actions to take
    """

    type Action = TacticApplication
    type Rollout = Generator[tuple[float, Action]]

    @abstractmethod
    def rollout(self, rdm: RocqDocManager, max_rollout: int | None = None) -> Rollout:
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


class CompositeStrategy(Strategy):
    """A (fair) combination of strategies"""

    def __init__(self, children: list[Strategy]) -> None:
        self._children = children

    @override
    def rollout(
        self, rdm: RocqDocManager, max_rollout: int | None = None
    ) -> Strategy.Rollout:
        def combine() -> Strategy.Rollout:
            queue: list[tuple[float, int, Strategy.Action, Strategy.Rollout]] = []
            for i, strat in enumerate(self._children):
                gen = strat.rollout(rdm, max_rollout=max_rollout)
                try:
                    pr, act = next(gen)
                except StopIteration:
                    continue
                heapq.heappush(queue, (pr, i, act, gen))

            while True:
                try:
                    (pr, i, act, gen) = queue.pop(0)
                except IndexError:
                    return
                yield (pr, act)
                try:
                    pr, act = next(gen)
                except StopIteration:
                    continue
                heapq.heappush(queue, (pr, i, act, gen))

        return combine()


class SafeTacticStrategy(Strategy):
    """A simple strategy that always returns a tactic."""

    def __init__(self, tactic: str, prob: float = 1.0) -> None:
        self._tactic = tactic
        self._prob = prob

    @override
    def rollout(
        self, rdm: RocqDocManager, max_rollout: int | None = None
    ) -> Strategy.Rollout:
        return (
            (prob, TacticApplication(tac)) for prob, tac in [(self._prob, self._tactic)]
        )


class CutAssertStrategy(SafeTacticStrategy):
    """A simple strategy that cuts a Rocq lemma.
    The success probability 1.0 is not necessarily appropriate."""

    def __init__(self, name: str, lemma: str, prob: float = 1.0) -> None:
        self._name: str = name
        self._lemma: str = lemma
        self._prob: float = prob

    @override
    def rollout(
        self, rdm: RocqDocManager, max_rollout: int | None = None
    ) -> Strategy.Rollout:
        name: str | RocqDocManager.Err = rdm.fresh_ident(self._name)
        if isinstance(name, RocqDocManager.Err):
            return empty_Rollout()
        tac: str = f"assert ({self._lemma}) as {name}"

        return ((prob, TacticApplication(t)) for prob, t in [(self._prob, tac)])


def empty_Rollout() -> Strategy.Rollout:
    yield from ()


class FailStrategy(Strategy):
    """A simple strategy that fails."""

    def __init__(self) -> None:
        pass

    @override
    def rollout(
        self, rdm: RocqDocManager, max_rollout: int | None = None
    ) -> Strategy.Rollout:
        return empty_Rollout()


# ----------------- Likely to be decommissioned Strategies -----------------#
class TryTacticStrategy(SafeTacticStrategy):
    """A simple strategy that emits 'try (tac)' for tactic tac.
    Success probability 1.0 is inherited from SafeTacticStrategy and appropriate."""

    def __init__(self, tac: str) -> None:
        super().__init__(f"try ({tac})")


class FirstTacticStrategy(Strategy):
    """A simple strategy creates the tactic 'first [ t1 | .. | tn ]' ).
    The success probability 1.0 is tha max of the individual strategies."""

    def __init__(self, tactics: list[tuple[float, str]]) -> None:
        self._tactics = tactics

    @override
    def rollout(
        self, rdm: RocqDocManager, max_rollout: int | None = None
    ) -> Strategy.Rollout:
        maxprob = max(prob for prob, _ in self._tactics)
        tacs = [item[1] for item in self._tactics]
        tacs_string = " | ".join(tacs)
        first_tac = f"first [{tacs_string}]"
        return ((prob, TacticApplication(tac)) for prob, tac in [(maxprob, first_tac)])
