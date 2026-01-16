from __future__ import annotations

from typing import Annotated, override

from provenance_toolkit import Provenance
from rocq_doc_manager import RocqCursor

from ...proof_state import ProofState, RocqGoal
from ..action import Action
from ..strategy import GuardStrategy, Strategy, empty_Rollout
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


class CutAssertStrategy(Strategy):
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


class FirstTacticStrategy(Strategy):
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


class FocusStrategy(GuardStrategy[RocqCursor, RocqGoal]):
    """A strategy that focuses on the first goal."""

    @override
    def check(
        self, rdm: RocqCursor, context: Strategy.Context | None = None
    ) -> RocqGoal | None:
        goal_reply = rdm.current_goal()
        if goal_reply is None:
            return None
        try:
            pf_state = ProofState(
                rdm.current_goal(),
            )
            if pf_state is None:
                raise RuntimeError(f"Failed to get structured proof state: {pf_state}")

            if len(pf_state.focused_goals) < 2:
                return None
            return pf_state.goal()
        except Exception:
            return None

    @override
    def rollout_with(
        self,
        val: RocqGoal,
        rdm: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        return self.rollout_goal(rdm, val, max_rollout, context)

    @override
    def rollout_goal(
        self,
        rdm: RocqCursor,
        rocqgoal: RocqGoal,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        print("FocusRollout: emitting {")
        return ((prob, RocqTacticAction(tac)) for prob, tac in [(1.0, " { ")])


class UnfocusStrategy(GuardStrategy[RocqCursor, ProofState]):
    """A strategy that ends the focus on the first goal.
    The WITH parameter is 'ProofState' rather than RocqGoal
    since in cases where the first goal has just been closed,
    there's no first_goal."""

    @override
    def check(
        self, rdm: RocqCursor, context: Strategy.Context | None = None
    ) -> ProofState | None:
        goal_reply = rdm.current_goal()
        if goal_reply is None:
            return None
        try:
            pf_state = ProofState(
                rdm.current_goal(),
            )
            if pf_state is None:
                raise RuntimeError(f"Failed to get structured proof state: {pf_state}")

            if len(pf_state.focused_goals) == 0 and len(pf_state.unfocused_goals) > 0:
                return pf_state
            else:
                return None
        except Exception:
            return None

    @override
    def rollout_with(
        self,
        val: ProofState,
        rdm: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        return self.rollout_goal(rdm, val, max_rollout, context)

    @override
    def rollout_goal(
        self,
        rdm: RocqCursor,
        pf: ProofState,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        return ((prob, RocqTacticAction(tac)) for prob, tac in [(1.0, " } ")])
