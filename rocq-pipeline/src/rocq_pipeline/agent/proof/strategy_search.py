from __future__ import annotations

import heapq
import math
from dataclasses import dataclass
from typing import Any, override

from rocq_doc_manager import RocqCursor

from rocq_pipeline.agent.base import TaskResult
from rocq_pipeline.agent.base.classes import ProofAgent
from rocq_pipeline.proof_state import ProofState
from rocq_pipeline.search import Action
from rocq_pipeline.search.rocq.manip import RocqManipulator
from rocq_pipeline.search.search import (
    DFS,
    Frontier,
    PQueue,
    SavingSolutions,
    StateManipulator,
)
from rocq_pipeline.search.search import search as search_strategy
from rocq_pipeline.search.strategy import Strategy


class SearchAgent(ProofAgent, VERSION="0.1.0"):
    """
    A simple search agent based on strategies.
    """

    def __init__(self, strategy: Strategy[RocqCursor], fuel: int | None = 100) -> None:
        self._strategy = strategy
        self._fuel = fuel

    @dataclass(order=True)
    class State:
        log_prob: float  # negative
        depth: int  # negative
        cursor: RocqCursor
        rollout: Strategy.Rollout

    class Manipulator(StateManipulator[State]):
        def __init__(self) -> None:
            self._rocq = RocqManipulator()

        def copy(self, state: SearchAgent.State) -> SearchAgent.State:
            return SearchAgent.State(
                state.log_prob,
                state.depth,
                self._rocq.copy(state.cursor),
                state.rollout,
            )

        def dispose(self, state: SearchAgent.State) -> None:
            self._rocq.dispose(state.cursor)

    @override
    def prove(self, rc: RocqCursor) -> TaskResult:
        def mk_frontier() -> Frontier[SearchAgent.State, Any]:
            def cmp(st1: SearchAgent.State, st2: SearchAgent.State) -> int:
                if st1.depth != st2.depth:
                    # Prefer deeper nodes
                    return st1.depth - st2.depth
                if st1.log_prob < st2.log_prob:
                    return -1
                if st1.log_prob > st2.log_prob:
                    return 1
                return 0

            base = PQueue(lambda x: x, cmp)
            return SavingSolutions(base, lambda st: True, stop_on_first_solution=True)

        init = SearchAgent.State(-math.log(1.0), 0, rc, self._strategy.rollout(rc))
        search_strategy(
            self._strategy, init, mk_frontier, state_manip=RocqManipulator()
        )

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
                prob, action = next(state.rollout)
                heapq.heappush(
                    states, state
                )  # push again in case there are more elements in the rollout
            except StopIteration:
                # This is just pruning an empty rollout
                state.cursor.dispose()
                iteration -= 1
                continue

            # A more efficient implementation of this might delay the
            # clone operation and only do it on success and then it would
            # revert. This avoids the creation of a cursor when the action
            # ultimately fails (which is probably common).
            fresh_rc = state.cursor.clone()
            try:
                result_rc = action.interact(fresh_rc)
            except Action.Failed:
                # the action failed, so we discard this
                fresh_rc.dispose()
                continue
            if result_rc != fresh_rc:
                fresh_rc.dispose()

            pf_state = ProofState(result_rc.current_goal())
            if pf_state.closed(proof=True):
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
