import heapq
import math
from dataclasses import dataclass
from typing import Annotated, override

from provenance_toolkit import Provenance
from rocq_doc_manager import RocqCursor

from rocq_pipeline.agent.base import TaskResult
from rocq_pipeline.agent.base.classes import ProofAgent
from rocq_pipeline.proof_state import ProofState
from rocq_pipeline.search import Action
from rocq_pipeline.search.rollout import Rollout
from rocq_pipeline.search.strategy import Strategy


class SearchAgent(ProofAgent):
    """
    A simple search agent based on strategies.
    """

    _strategy: Annotated[Strategy, Provenance.Reflect.Field]
    _fuel: Annotated[int | None, Provenance.Reflect.Field]

    def __init__(self, strategy: Strategy, fuel: int | None = 100) -> None:
        self._strategy = strategy
        self._fuel = fuel

    @dataclass(order=True)
    class State:
        log_prob: float  # negative
        depth: int  # negative
        fresh: int  # just to break ties
        cursor: RocqCursor
        rollout: Rollout[Action[RocqCursor]]

    @override
    async def prove(self, rc: RocqCursor) -> TaskResult:
        next_id: int = 0

        def fresh() -> int:
            nonlocal next_id
            next_id += 1
            return next_id

        states: list[SearchAgent.State] = []
        heapq.heappush(
            states,
            SearchAgent.State(
                -math.log(1.0), 0, fresh(), rc, await self._strategy.rollout(rc)
            ),
        )

        iteration: int = 0
        while self._fuel is None or iteration < self._fuel:
            iteration += 1
            if not states:
                break
            state = heapq.heappop(states)

            # TODO: this looks incorrect because the rollout is not actually used
            try:
                prob, action = await anext(state.rollout)
                heapq.heappush(
                    states, state
                )  # push again in case there are more elements in the rollout
            except StopAsyncIteration:
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
                result_rc = await action.interact(fresh_rc)
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
                await self._strategy.rollout(fresh_rc),
            )
            heapq.heappush(states, next_state)
        return self.give_up(rc, "out of fuel")
