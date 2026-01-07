from __future__ import annotations

from typing import Any, override

from observability import get_logger
from provenance_toolkit import Provenance
from rocq_doc_manager import RocqCursor

from rocq_pipeline.proof_state import ProofState, RocqGoal
from rocq_pipeline.schema import task_output
from rocq_pipeline.schema.task_output import FailureReason

from .dataclasses import (
    TacticApplication,
    TaskResult,
)

logger = get_logger("rocq_agent")


class Agent(Provenance.Full):
    """Abstract base class for Rocq Agent Toolkit agents."""

    def run(self, rdm: RocqCursor) -> TaskResult:
        """Entrypoint; use rdm to attempt a task and report the result."""
        return self.give_up(rdm, message="Not implemented")

    @classmethod
    def cls_name(cls) -> str:
        """Return the unique name for this type of agent."""
        return cls.__qualname__

    def name(self) -> str:
        """Return the unique name for an instance of this type of agent."""
        return self.cls_name()

    def finished(
        self,
        rdm: RocqCursor,
        message: str = "",
        side_effects: dict[str, Any] | None = None,
    ) -> TaskResult:
        """Create a TaskResult when the agent finishes successfully."""
        return TaskResult.finished(
            message=message,
            side_effects=side_effects,
            _metrics=self._task_metrics(),
        )

    def give_up(
        self,
        rdm: RocqCursor,
        message: str = "",
        reason: FailureReason | RocqCursor.Err | BaseException | None = None,
        side_effects: dict[str, Any] | None = None,
    ) -> TaskResult:
        """Create a TaskResult when the agent gives up."""
        if isinstance(reason, BaseException):
            return TaskResult.from_exception(
                reason,
                message=message,
                side_effects=side_effects,
                _metrics=self._task_metrics(),
            )
        return TaskResult.give_up(
            message=message,
            reason=reason,
            side_effects=side_effects,
            _metrics=self._task_metrics(),
        )

    # TODO: obviate this in favor of extensible use of opentelemetry
    def _task_metrics(self) -> task_output.Metrics:
        """Task specific metrics from working on the task."""
        return task_output.Metrics()


# TODO: incorporate AgentConfig
class AgentBuilder:
    """Builder class for Rocq Agent Toolkit agents."""

    def __init__(self, agent_type: type[Agent] = Agent):
        self._agent: type[Agent] = agent_type

    @staticmethod
    def of_agent(agent_type: type[Agent]) -> AgentBuilder:
        return AgentBuilder(agent_type)

    def add_args(self, args: list[str]) -> None:
        """Parse agent-specific args in preparation for building the agent."""
        pass

    def __call__(self, prompt: str | None = None) -> Agent:
        return self._agent()

    def extra_rocq_args(self) -> list[str]:
        return []


# TODO: integrate proof tree and structured proof states so that
# task_holes / task_doc_interaction can be defined in a more
# structured way.
class ProofAgent(Agent):
    """Agents tasked with completing proof obligations."""

    def __init__(self, goal_ty_upperbound: type[RocqGoal] = RocqGoal) -> None:
        if not issubclass(goal_ty_upperbound, RocqGoal):
            raise RuntimeError(f"{goal_ty_upperbound} is not a subclass of RocqGoal")
        self._goal_ty_upperbound = goal_ty_upperbound

    def prove(self, rc: RocqCursor) -> TaskResult:
        """Prove the current goal using the restricted proof session.

        This method is called by run() after setting up a RocqProofSession.
        Subclasses should implement their proof logic here.
        """
        return self.give_up(rc, message="Not implemented")

    @override
    def run(self, rc: RocqCursor) -> TaskResult:
        """Run the agent after ensuring there is a goal to prove."""
        goal_reply = rc.current_goal()
        if goal_reply is None:
            return self.finished(rc, message="No goal to prove")
        if isinstance(goal_reply, RocqCursor.Err):
            return self.give_up(rc, message="No goal to prove", reason=goal_reply)
        # TODO: validate that no goals remain.
        return self.prove(rc)

    def current_proof_state(
        self,
        rdm: RocqCursor,
        goal_ty_upperbound: type[RocqGoal] | None = None,
    ) -> ProofState | RocqCursor.Err[None]:
        """Structured view of the current proof state (via RDM.current_goal).

        Note: self._goal_ty_upperbound can be overriden."""
        if goal_ty_upperbound is None:
            goal_ty_upperbound = self._goal_ty_upperbound
        goal_reply = rdm.current_goal()
        if isinstance(goal_reply, RocqCursor.Err):
            return goal_reply
        return ProofState(
            goal_reply,
            goal_ty_upperbound=goal_ty_upperbound,
        )

    def run_tactic(
        self,
        rdm: RocqCursor,
        tac: str,
    ) -> TacticApplication:
        """Get the result of running tac using rdm, tracing the interaction."""
        tac_app = TacticApplication(tactic=tac)

        pre_pf_state_reply = self.current_proof_state(rdm)
        if isinstance(pre_pf_state_reply, RocqCursor.Err):
            tac_app.err = pre_pf_state_reply
            return tac_app
        else:
            tac_app.pf_state_pre = pre_pf_state_reply
        logger.info(
            "Tactic Pre State",
            pf_state_pre=tac_app.pf_state_pre.to_json(),
        )

        logger.info(
            "Tactic Application",
            tactic_application_tactic=tac,
        )
        tac_reply = rdm.run_command(tac)
        if isinstance(tac_reply, RocqCursor.Err):
            logger.info(
                "Tactic Application Status",
                status="Failure",
                error_msg=tac_reply.message,
                # error_data=tac_reply.data,
            )
            tac_app.err = tac_reply
            return tac_app
        logger.info(
            "Tactic Application Status",
            status="Success",
        )

        post_pf_state_reply = self.current_proof_state(rdm)
        if isinstance(post_pf_state_reply, RocqCursor.Err):
            tac_app.err = post_pf_state_reply
            return tac_app
        tac_app.pf_state_post = post_pf_state_reply
        logger.info(
            "Tactic Post State",
            pf_state_post=tac_app.pf_state_post.to_json(),
        )

        return tac_app
