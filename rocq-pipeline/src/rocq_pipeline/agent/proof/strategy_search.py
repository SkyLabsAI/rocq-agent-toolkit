import heapq
import math
from dataclasses import dataclass
from typing import override

from rocq_doc_manager import RocqCursor

from rocq_pipeline.agent.base import TaskResult
from rocq_pipeline.agent.base.classes import ProofAgent
from rocq_pipeline.agent.proof.strategy import Strategy


class SearchAgent(ProofAgent):
    """
    A simple search agent based on strategies.
    """

    def __init__(self, strategy: Strategy, fuel: int | None = 100) -> None:
        self._strategy = strategy
        self._fuel = fuel

    @dataclass(order=True)
    class State:
        log_prob: float  # negative
        depth: int  # negative
        fresh: int  # just to break ties
        cursor: RocqCursor
        rollout: Strategy.Rollout

    @override
    def prove(self, rc: RocqCursor) -> TaskResult:
        next_id: int = 0

        def fresh() -> int:
            nonlocal next_id
            next_id += 1
            return next_id

        states: list[SearchAgent.State] = []
        heapq.heappush(
            states,
            SearchAgent.State(
                -math.log(1.0), 0, fresh(), rc, self._strategy.rollout(rc)
            ),
        )

        iteration: int = 0
        while self._fuel is None or iteration < self._fuel:
            iteration += 1
            if not states:
                break
            state = heapq.heappop(states)

            try:
                prob, tac = next(state.rollout)
                heapq.heappush(
                    states, state
                )  # push again in case there are more elements in the rollout
            except StopIteration:
                # This is just pruning an empty rollout
                state.cursor.dispose()
                iteration -= 1
                continue

            fresh_rc = state.cursor.clone()
            tac_result = super().run_tactic(rc, tac)
            if tac_result.err is not None:
                # this tactic application did not succeed
                # for now, we abandon it, but, in the future, we might look for alternatives
                fresh_rc.dispose()
                continue

            assert tac_result.pf_state_post is not None
            if tac_result.pf_state_post.closed(proof=True):
                # TODO: this is an approximation due to shelved goals and such.
                return self.finished(fresh_rc, "done")

            next_state = SearchAgent.State(
                state.log_prob - math.log(prob),
                state.depth - 1,
                fresh(),
                fresh_rc,
                self._strategy.rollout(fresh_rc),
            )
            heapq.heappush(states, next_state)
        return self.give_up(rc, "out of fuel")
