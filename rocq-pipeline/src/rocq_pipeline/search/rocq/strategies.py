"""
A collection of various algorithmic strategies for Rocq.
"""

from __future__ import annotations

import math
from typing import Annotated, override

from provenance_toolkit import Provenance
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

from ..action import Action
from ..rollout import ApproximatingRollout, EmptyRollout, Rollout, singleton
from ..strategy import Strategy
from .actions import RocqTacticAction, ensure_tactic


class SafeTacticStrategy(Strategy[RocqCursor, Action[RocqCursor]]):
    """A simple strategy that always returns a tactic."""

    _tactic: Annotated[str, Provenance.Reflect.Field]
    _score: Annotated[float, Provenance.Reflect.Field]

    # TODO: this is a logprob
    def __init__(self, tactic: str, prob: float = 0.0) -> None:
        """The `tactic` is a Rocq tactic, **not** a Rocq command,
        therefore, there should be no '.'"""
        super().__init__()
        ensure_tactic(tactic)
        self._score = prob
        self._tactic = tactic
        self._prob = prob

    @override
    async def rollout(
        self,
        state: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action[RocqCursor]]:
        return singleton(
            RocqTacticAction(f"progress ({self._tactic})"), score=self._score
        )


class CutAssertStrategy(Strategy):
    """A simple strategy that cuts a Rocq lemma.
    The success probability 0.1 is not necessarily appropriate."""

    def __init__(self, name: str, lemma: str, prob: float = 0.1) -> None:
        self._name: str = name
        self._lemma: str = lemma
        self._logprob: float = math.log(prob)

    @override
    async def rollout(
        self,
        state: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action[RocqCursor]]:
        name: str | rdm_api.Err[None] = await state.fresh_ident(self._name)
        if isinstance(name, rdm_api.Err):
            return EmptyRollout()

        # For now, it is important that we fail if this fact is already known,
        # otherwise we risk looping here
        tac: str = f"assert ({self._lemma}) as {name}; [ assert_fails tauto | ]"

        return singleton(RocqTacticAction(tac), score=math.log(self._logprob))


class FirstTacticStrategy(Strategy[RocqCursor, Action[RocqCursor]]):
    """A simple strategy that tries each of the given tactics with their given probabilities."""

    _tactics: Annotated[
        list[tuple[float, Action[RocqCursor]]], Provenance.Reflect.Field
    ]

    def __init__(self, tactics: list[tuple[float, str | Action[RocqCursor]]]) -> None:
        def mk(x: str | Action[RocqCursor]) -> Action[RocqCursor]:
            if isinstance(x, Action):
                return x
            return RocqTacticAction(x)

        self._tactics: list[tuple[float, Action[RocqCursor]]] = [
            (prob, mk(tac)) for prob, tac in sorted(tactics, reverse=True)
        ]

    @override
    async def rollout(
        self,
        state: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action[RocqCursor]]:
        return ApproximatingRollout(
            (
                Rollout.Approx(logprob=prob, result=result)
                for prob, result in self._tactics
            )
        )
