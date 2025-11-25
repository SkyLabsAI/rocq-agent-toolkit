from abc import ABC, abstractmethod
from typing import Any, override

from observability import get_logger
from rocq_doc_manager import RocqDocManager

from rocq_pipeline.proof_state import ProofState, RocqGoal
from rocq_pipeline.schema import task_output
from rocq_pipeline.schema.task_output import ExecutionError, FailureReason

from .dataclasses import (
    # AgentConfig,
    Finished,
    GiveUp,
    TacticApplication,
)

logger = get_logger("rocq_agent")


class Agent(ABC):
    """Abstract base class for Rocq Agent Toolkit agents."""
    # TODOS:
    # 1) consider threading some task information into the [run] call
    # 2) consider allowing for restricted task mutation/elaboration/refinement
    #    based on (sub)agent behavior
    @abstractmethod
    def run(self, rdm: RocqDocManager) -> Finished | GiveUp:
        """Entrypoint; use [rdm] to attempt a task and report the result."""
        ...

    # TODO: obviate this in favor of extensible use of opentelemetry
    @abstractmethod
    def task_metrics(self) -> task_output.Metrics:
        """Task specific metrics from working on the task."""
        ...

    @abstractmethod
    def task_holes(self, rdm: RocqDocManager) -> Any:
        """Task specific holes that remain for the task."""
        ...

    @abstractmethod
    def task_doc_interaction(self, rdm: RocqDocManager) -> Any:
        """Task specific document interactions the agent wants to report."""
        ...

    def task_holes_json(self, rdm: RocqDocManager) -> Any:
        return self.task_holes(rdm)

    def task_doc_interaction_json(self, rdm: RocqDocManager) -> Any:
        return self.task_doc_interaction(rdm)

    @classmethod
    def cls_name(cls) -> str:
        """Return the unique name for this type of agent."""
        # NOTE: derivers will automatically get a reasonable name based on
        # (nested) class name.
        return cls.__qualname__

    def name(self) -> str:
        """Return the unique name for an instance of this type of agent."""
        return self.cls_name()

    def task_finished(self, rdm: RocqDocManager) -> bool:
        """Task specific predicate indicating whether the task is finished."""
        # Note: by default, we consider a task finished when there are no
        # more task-specific holes.
        holes = self.task_holes(rdm)
        if isinstance(holes, RocqDocManager.Err):
            logger.warning(
                f"{self.name()}.task_finished: task_holes returned an error"
            )
            return False
        return not bool(holes)

    def finished(
            self,
            rdm: RocqDocManager,
            message: str | None = None,
    ) -> Finished:
        data = {
            "metrics": self.task_metrics(),
            "final_doc_interaction": self.task_doc_interaction_json(rdm),
            "final_holes": self.task_holes_json(rdm),
        }
        if message is not None:
            data["message"] = message

        return Finished(**data)

    def give_up(
            self,
            rdm: RocqDocManager,
            reason: FailureReason | RocqDocManager.Err | BaseException,
    ) -> GiveUp:
        rdm.doc_prefix()
        is_exception = issubclass(type(reason), BaseException)
        is_rdm_err = issubclass(type(reason), RocqDocManager.Err)
        if is_exception or is_rdm_err:
            reason = FailureReason(ExecutionError(str(reason)))
        data = {
            "metrics": self.task_metrics(),
            "final_doc_interaction": self.task_doc_interaction_json(rdm),
            "final_holes": self.task_holes_json(rdm),
            "reason": reason,
        }

        return GiveUp(**data)


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
    @override
    def run(self, rdm: RocqDocManager) -> Finished | GiveUp:
        return self.give_up(
            rdm,
            reason=NotImplementedError(
                f"{self.name()}.run"
            ),
        )

    def run_tactic(
            self,
            rdm: RocqDocManager,
            tac: str,
            goal_ty_bound: type[RocqGoal] = RocqGoal,
    ) -> TacticApplication:
        """Get the result of running tac using rdm, tracing the interaction."""
        tac_app = TacticApplication(tactic=tac)

        pre_goal_reply = rdm.current_goal()
        if isinstance(pre_goal_reply, RocqDocManager.Err):
            tac_app.err = pre_goal_reply
            return tac_app
        tac_app.pf_state_pre = ProofState(
            pre_goal_reply,
            goal_ty_bound=goal_ty_bound,
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
        else:
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
                goal_ty_bound=goal_ty_bound,
            )
        logger.info(
            "Tactic Post State",
            pf_state_post=tac_app.pf_state_post.to_json(),
        )

        return tac_app

    @override
    def task_metrics(self) -> task_output.Metrics:
        return task_output.Metrics()

    @override
    def task_holes(
            self,
            rdm: RocqDocManager,
            goal_ty_bound: type[RocqGoal] = RocqGoal,
    ) -> ProofState | RocqDocManager.Err:
        current_goal_reply = rdm.current_goal()
        if isinstance(current_goal_reply, RocqDocManager.Err):
            return current_goal_reply
        return ProofState(
            current_goal_reply,
            goal_ty_bound=goal_ty_bound
        )

    @override
    def task_holes_json(
            self,
            rdm: RocqDocManager,
            goal_ty_bound: type[RocqGoal] = RocqGoal,
    ) -> dict[int, Any] | str:
        holes = self.task_holes(rdm, goal_ty_bound=goal_ty_bound)
        if isinstance(holes, RocqDocManager.Err):
            return str(holes)
        else:
            return holes.to_json()

    @override
    def task_doc_interaction(self, rdm: RocqDocManager) -> str:
        logger.warning(" ".join([
            "missing real implementation for",
            f"{self.name()}.task_doc_interaction",
        ]))
        return ""
