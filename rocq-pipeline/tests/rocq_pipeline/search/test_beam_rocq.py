"""Test beam search with a Rocq problem."""

from __future__ import annotations

from rocq_doc_manager import RocqCursor
from rocq_pipeline.search.rocq.actions import TacticAction
from rocq_pipeline.search.rocq.strategies import SafeTacticStrategy

try:
    from typing import override
except ImportError:
    from typing import override

from rocq_pipeline.search.search.beam import BeamSearch
from rocq_pipeline.search.strategy import CompositeStrategy, Strategy


class CustomStrategy(Strategy[RocqCursor]):
    @override
    def rollout(
        self,
        state: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout[RocqCursor]:
        pf: RocqCursor.ProofState = state.current_goal()
        if "induction a; simpl; auto." in [
            text.text for text in state.doc_prefix() if text.kind == "command"
        ]:
            return iter(
                [
                    (0.65, TacticAction("fail")),
                    (0.25, TacticAction("rewrite add_S; congruence.")),
                    (0.1, TacticAction("idtac")),
                ]
            )
        else:
            return iter(
                [
                    (0.65, TacticAction("fail")),
                    (0.25, TacticAction("induction a; simpl; auto.")),
                    (0.1, TacticAction("idtac")),
                ]
            )

        return super().rollout(state, max_rollout, context)


def test_my_nat_add_zero() -> None:
    """Test that beam search can find a nearby target."""

    # This is a simple strategy that should work
    strat = CompositeStrategy(
        [
            SafeTacticStrategy("induction a; simpl; auto.", 0.5),
            SafeTacticStrategy("rewrite add_S; congruence.", 0.5),
        ]
    )

    start = GridState(0, 0)
    target = GridState(2, 1)

    guidance = ManhattanGuidance(target)
    strategy = GridStrategy()

    search = BeamSearch(
        strategy=strategy,
        guidance=guidance,
        is_solved=lambda s: s == target,
        beam_width=3,
        explore_width=4,
        max_depth=10,
        stop_on_first_solution=True,
        state_key=lambda s: (s.x, s.y),  # Deduplicate by position
    )

    solutions = search.search(start)

    assert len(solutions) > 0, "Should find at least one solution"
    assert target in solutions, f"Should find target {target}, got {solutions}"
