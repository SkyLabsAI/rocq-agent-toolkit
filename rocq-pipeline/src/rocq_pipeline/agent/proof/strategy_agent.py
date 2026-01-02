import itertools
import time
from dataclasses import dataclass
from typing import override

from rocq_doc_manager import RocqCursor

from rocq_pipeline.agent import (
    TaskResult,
)
from rocq_pipeline.agent.base import ProofAgent
from rocq_pipeline.proof_state import ProofState, RocqGoal
from observability import get_logger
from rocq_pipeline.search.action import Action
from rocq_pipeline.search.strategy import Strategy

logger = get_logger("rocq_agent")


class StrategyAgent(ProofAgent, VERSION="0.1.0"):
    """An agent that uses a Strategy to select tactics."""

    def __init__(
        self,
        strategy: Strategy,
        max_depth: int | None = None,
        max_breath: int | None = None,
        fuel: int | None = None,
    ) -> None:
        super().__init__(goal_ty_upperbound=RocqGoal)
        self._strategy = strategy
        self._max_depth = max_depth
        self._max_breath = max_breath
        self._fuel = fuel

    def prepare(self, rc: RocqCursor) -> None:
        pass

    @dataclass
    class NoProofState(Exception):
        reason: RocqCursor.Err

    def _current_state(self, rc: RocqCursor) -> ProofState:
        reply = rc.current_goal()
        if isinstance(reply, RocqCursor.Err):
            raise StrategyAgent.NoProofState(reply)
        return ProofState(reply)

    @override
    def prove(self, rc: RocqCursor) -> TaskResult:
        self.prepare(rc)

        start_time = time.monotonic()
        depth: int = 0
        rem_fuel: int | None = self._fuel
        while True:
            state = self._current_state(rc)
            if state.closed(proof=True):
                return self.finished(rc)

            if self._max_depth is not None and depth >= self._max_depth:
                return self.give_up(
                    rc,
                    message=f"depth limit exceeded({self._max_depth})",
                )

            rollout = self._strategy.rollout(rc)
            for _, action in (
                rollout
                if self._max_breath is None
                else itertools.islice(rollout, self._max_breath)
            ):
                if rem_fuel is not None:
                    rem_fuel -= 1
                    if rem_fuel <= 0:
                        return self.give_up(rc, message=f"out of fuel ({self._fuel})")
                action_key = action.key()
                logger.info("Tactic Pre State", pf_state_pre=state.to_json())
                logger.info(
                    "Tactic Application",
                    tactic_application_tactic=action_key,
                )
                action_rc = rc.clone()
                try:
                    action.interact(action_rc)
                    logger.info(
                        "Tactic Application Status",
                        status="Success",
                    )
                    try:
                        post_state = self._current_state(action_rc)
                        logger.info(
                            "Tactic Post State",
                            pf_state_post=post_state.to_json(),
                        )
                    except StrategyAgent.NoProofState:
                        logger.warning(
                            "Tactic Post State",
                            error_msg="Failed to read post-state",
                        )
                    rc = action_rc
                    depth += 1
                    logger.info(
                        "Depth Progress",
                        depth=depth,
                        elapsed_seconds=time.monotonic() - start_time,
                        remaining_fuel=rem_fuel,
                    )
                    break
                except Action.Failed as e:
                    action_rc.dispose()
                    logger.info(
                        "Tactic Application Status",
                        status="Failure",
                        error_msg=e.message,
                    )
            else:
                # not executed if we see a break
                return self.give_up(
                    rc, f"No more proposals (max_breath={self._max_breath}"
                )
