from typing import override

from rocq_doc_manager import RocqCursor

from rocq_pipeline.agent import (
    TaskResult,
    TraceAgent,
)
from rocq_pipeline.agent.proof.strategy import Strategy
from rocq_pipeline.proof_state import RocqGoal


class StrategyAgent(TraceAgent):
    """An agent that uses a Strategy to select tactics."""

    def __init__(self, strategy: Strategy) -> None:
        super().__init__(goal_ty_upperbound=RocqGoal)
        self._strategy = strategy
        self._rollout: Strategy.Rollout | None = None

    @override
    def next_tac(self, rdm: RocqCursor) -> str | TaskResult:
        if self._rollout is None or not self.last_failed():
            self._rollout = self._strategy.rollout(rdm)
        try:
            _, action = next(self._rollout)
            return action.tactic
        except StopIteration:
            return self.give_up(rdm, message="No more tactics in rollout after failure")
