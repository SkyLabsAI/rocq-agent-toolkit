from typing import Any, override
import os
from observability import get_logger
from rocq_doc_manager import RocqDocManager

from rocq_pipeline.proof_state import ProofState, RocqGoal
from rocq_pipeline.schema import task_output
from rocq_pipeline.schema.task_output import FailureReason

from .dataclasses import (
    TacticApplication,
    # AgentConfig,
    TaskResult,
)

logger = get_logger("rocq_agent")


class Agent:
    """Abstract base class for Rocq Agent Toolkit agents."""

    def run(self, rdm: RocqDocManager) -> TaskResult:
        """Entrypoint; use rdm to attempt a task and report the result."""
        return self.give_up(rdm, message="Not implemented")

    @classmethod
    def cls_name(cls) -> str:
        """Return the unique name for this type of agent."""
        return cls.__qualname__

    def name(self) -> str:
        """Return the unique name for an instance of this type of agent."""
        # EXP : Change agent name based on the environment variables.
        if os.getenv("AGENT_NAME"):
            return os.getenv("AGENT_NAME")
        return self.cls_name()

    def finished(
        self,
        rdm: RocqDocManager,
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
        rdm: RocqDocManager,
        message: str = "",
        reason: FailureReason | RocqDocManager.Err | BaseException | None = None,
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
    def of_agent(agent_type: type[Agent]) -> "AgentBuilder":
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

    def prove(self, rdm: RocqDocManager) -> TaskResult:
        """Prove the current goal using the restricted proof session.

        This method is called by run() after setting up a RocqProofSession.
        Subclasses should implement their proof logic here.
        """
        return self.give_up(rdm, message="Not implemented")

    @override
    def run(self, rdm: RocqDocManager) -> TaskResult:
        """Run the agent after ensuring there is a goal to prove."""
        goal_reply = rdm.current_goal()
        if goal_reply is None:
            return self.finished(rdm, message="No goal to prove")
        if isinstance(goal_reply, RocqDocManager.Err):
            return self.give_up(rdm, message="No goal to prove", reason=goal_reply)
        # TODO: validate that no goals remain.
        return self.prove(rdm)

    def run_tactic(
        self,
        rdm: RocqDocManager,
        tac: str,
    ) -> TacticApplication:
        """Get the result of running tac using rdm, tracing the interaction."""
        tac_app = TacticApplication(tactic=tac)

        pre_goal_reply = rdm.current_goal()
        if isinstance(pre_goal_reply, RocqDocManager.Err):
            tac_app.err = pre_goal_reply
            return tac_app
        tac_app.pf_state_pre = ProofState(
            pre_goal_reply,
            goal_ty_upperbound=self._goal_ty_upperbound,
        )
        logger.info(
            "Tactic Pre State",
            pf_state_pre=tac_app.pf_state_pre.to_json(),
        )

        logger.info(
            "Tactic Application",
            tactic_application_tactic=tac,
        )
        tac_reply = rdm.run_command(tac)
        if isinstance(tac_reply, RocqDocManager.Err):
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

        post_goal_reply = rdm.current_goal()
        if isinstance(post_goal_reply, RocqDocManager.Err):
            tac_app.err = post_goal_reply
            return tac_app
        tac_app.pf_state_post = ProofState(
            post_goal_reply,
            goal_ty_upperbound=self._goal_ty_upperbound,
        )
        logger.info(
            "Tactic Post State",
            pf_state_post=tac_app.pf_state_post.to_json(),
        )

        return tac_app
