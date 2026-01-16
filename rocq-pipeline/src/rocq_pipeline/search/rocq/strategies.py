from __future__ import annotations

from typing import Annotated, override

from provenance_toolkit import Provenance
from rocq_doc_manager import RocqCursor

from ..action import Action
from ..strategy import Strategy, empty_Rollout
from .actions import RocqTacticAction


class SafeTacticStrategy(Strategy[RocqCursor]):
    """A simple strategy that always returns a tactic."""

    _tactic: Annotated[str, Provenance.Reflect.Field]
    _prob: Annotated[float, Provenance.Reflect.Field]

    def __init__(self, tactic: str, prob: float = 1.0) -> None:
        self._tactic = tactic
        self._prob = prob

    @override
    def rollout(
        self,
        rdm: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        return (
            (prob, RocqTacticAction(f"progress ({tac})"))
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
        self,
        rdm: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        name: str | RocqCursor.Err[None] = rdm.fresh_ident(self._name)
        if isinstance(name, RocqCursor.Err):
            return empty_Rollout()

        # For now, it is important that we fail if this fact is already known,
        # otherwise we risk looping here
        tac: str = f"assert ({self._lemma}) as {name}; [ assert_fails tauto | ]"

        return ((prob, RocqTacticAction(t)) for prob, t in [(self._prob, tac)])


class FirstTacticStrategy(Strategy[RocqCursor]):
    """A simple strategy that tries each of the given tactics with their given probabilities."""

    _tactics: Annotated[list[tuple[float, Action]], Provenance.Reflect.Field]

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
        self,
        rdm: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        return ((prob, tac) for prob, tac in self._tactics)
