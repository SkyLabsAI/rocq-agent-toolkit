from __future__ import annotations

import math
from typing import override

from rocq_doc_manager import RocqCursor

from ..action import Action
from ..rollout import EmptyRollout, IteratorRollout, Rollout, SingletonRollout
from ..strategy import Strategy
from .actions import RocqTacticAction


class SafeTacticStrategy(Strategy):
    """A simple strategy that always returns a tactic."""

    def __init__(self, tactic: str, prob: float = 1.0) -> None:
        self._tactic: str = tactic
        self._logprob: float = math.log(prob)

    @override
    def rollout(
        self,
        rdm: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action[RocqCursor]]:
        return SingletonRollout(
            RocqTacticAction("progress {tac}"), logprob=self._logprob
        )


class CutAssertStrategy(Strategy):
    """A simple strategy that cuts a Rocq lemma.
    The success probability 1.0 is not necessarily appropriate."""

    def __init__(self, name: str, lemma: str, prob: float = 1.0) -> None:
        self._name: str = name
        self._lemma: str = lemma
        self._logprob: float = math.log(prob)

    @override
    def rollout(
        self,
        rdm: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action[RocqCursor]]:
        name: str | RocqCursor.Err[None] = rdm.fresh_ident(self._name)
        if isinstance(name, RocqCursor.Err):
            return EmptyRollout()

        # For now, it is important that we fail if this fact is already known,
        # otherwise we risk looping here
        tac: str = f"assert ({self._lemma}) as {name}; [ assert_fails tauto | ]"

        return SingletonRollout(RocqTacticAction(tac), logprob=math.log(self._logprob))


class FirstTacticStrategy(Strategy):
    """A simple strategy that tries each of the given tactics with their given probabilities."""

    def __init__(self, tactics: list[tuple[float, str | Action[RocqCursor]]]) -> None:
        def mk(x: str | Action[RocqCursor]) -> Action[RocqCursor]:
            if isinstance(x, Action):
                return x
            return RocqTacticAction(x)

        self._tactics: list[Rollout.Approx[Action[RocqCursor]]] = [
            Rollout.Approx(prob, mk(tac)) for prob, tac in sorted(tactics, reverse=True)
        ]

    @override
    def rollout(
        self,
        rdm: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action[RocqCursor]]:
        return IteratorRollout(iter(self._tactics))
