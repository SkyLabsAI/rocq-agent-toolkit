import pprint
from dataclasses import dataclass, field
import inspect
from typing import Any, override

from rocq_doc_manager import RocqDocManager
from rocq_pipeline.schema import task_output
from rocq_pipeline.schema.task_output import (
    ExecutionError,
    FailureReason,
    ProofVerificationFailed
)


def close_proof(rdm: RocqDocManager) -> None:
    assert isinstance(rdm.run_command("Qed."), RocqDocManager.Resp)


@dataclass
class TaskResult:
    """The final doc interaction that yielded the result."""
    final_doc_interaction: str
    message: str


@dataclass
class GiveUp(TaskResult):
    message: str = field(init=False)
    reason: task_output.FailureReason

    def __post_init__(self) -> None:
        self.message = f"failure: {str(self.reason)}"


@dataclass
class Finished(TaskResult):
    message: str = "success"


@dataclass
class Tactic:
    tactic: str


class Agent:
    def get_code_info(self) -> task_output.CodeInfo:
        # Get code info using inspection
        try:
            file_path = inspect.getfile(self.__class__)
            _, start_line = inspect.getsourcelines(self.__class__)
        except (OSError, TypeError):
            file_path = "unknown"
            start_line = 0

        # Try to get git info (TODO: implement actual git detection)
        git_repo = "unknown"
        git_sha = "unknown"

        return task_output.CodeInfo(
            git_repo=git_repo,
            git_sha=git_sha,
            file_path=file_path,
            class_name=self.__class__.__name__,
            start_line=start_line,
        )

    def get_subagent_metadata(self) -> list[task_output.AgentMetadata]:
        return []

    def get_model_info(self) -> task_output.ModelInfo | None:
        return None

    def get_metadata(self) -> task_output.AgentMetadata:
        return task_output.AgentMetadata(
            code_info=self.get_code_info(),
            sub_agents=self.get_subagent_metadata(),
            model_info=self.get_model_info(),
        )

    def run(self, rdm: RocqDocManager) -> Finished | GiveUp:
        # Suppress unused argument warning for base class
        _ = rdm
        return GiveUp(
            final_doc_interaction="",
            reason=FailureReason(task_output.Other("not implemented"))
        )


class OneShotAgent(Agent):
    _tactic: str = "idtac"

    def __init__(self, tactic: str) -> None:
        self._tactic = tactic

    @override
    def run(self, rdm: RocqDocManager) -> Finished | GiveUp:
        solve_tac = f"solve [ {self._tactic} ]."
        final_doc_interaction: str = solve_tac
        if isinstance(rdm.run_command(solve_tac), RocqDocManager.Err):
            return GiveUp(
                final_doc_interaction,
                reason=FailureReason(ProofVerificationFailed())
            )
        return Finished(final_doc_interaction)


# NOTE: this agent does not support backtracking
class TraceAgent(Agent):
    def __init__(self, stop_on_failure: bool = False) -> None:
        self._stop_on_failure = stop_on_failure
        # Each element of [_history] is a tactic and a boolean indicating
        # whether its application succeeded.
        self._history: list[tuple[Tactic, bool]] = list()

    def last_failed(self) -> bool:
        if not self._history:
            return False

        return self._history[-1][1]

    def update_history(self, tactic: Tactic, success: bool = True) -> None:
        self._history.append((tactic, success))

    def history(self) -> list[tuple[Tactic, bool]]:
        # Note: return a shallow copy of the history
        return self._history[:]

    def final_doc_interaction(self) -> str:
        return "\n".join([
            f"{tactic.tactic}."
            for tactic, success in self._history
            if success
        ])

    @override
    def run(self, rdm: RocqDocManager) -> Finished | GiveUp:
        should_trace = True

        def trace(msg: str, data: Any | None = None) -> None:
            if should_trace:
                print(msg)
                if data:
                    pprint.pprint(data, width=200)

        # Start trying to verify the code
        #
        # TODO: add fuel to guard against agents that never give up
        # and never succeed.
        while True:
            if self._stop_on_failure and self.last_failed():
                return self.give_up(
                    FailureReason(ExecutionError()),
                )

            if should_trace:
                goal = rdm.current_goal()
                trace("Current Goal:", data=goal)

            tactic: Tactic | GiveUp = self.next(rdm)
            trace("Tactic:", data=tactic)

            if isinstance(tactic, GiveUp):
                return tactic

            result = rdm.run_command(f"{tactic.tactic}.")
            if isinstance(result, rdm.Resp):
                self.update_history(tactic)
                if result.result["open_subgoals"] == "No more goals.":
                    return self.finished()
            elif isinstance(result, rdm.Err):
                self.update_history(tactic, success=False)
                trace("Failed", data=result)
                self.failed(result)

    def next(self, rdm: RocqDocManager) -> Tactic | GiveUp:
        # Suppress unused argument warning for base class
        _ = rdm
        return self.give_up(
            FailureReason(task_output.Other("not implemented"))
        )

    def failed(self, err: RocqDocManager.Err) -> None:
        # Base implementation does nothing - subclasses can override
        _ = err

    def finished(self, message: str | None = None) -> Finished:
        final_doc_interaction = self.final_doc_interaction()
        if message:
            return Finished(
                message=message,
                final_doc_interaction=final_doc_interaction
            )
        else:
            return Finished(
                final_doc_interaction=final_doc_interaction
            )

    def give_up(self, reason: FailureReason) -> GiveUp:
        return GiveUp(
            final_doc_interaction=self.final_doc_interaction(),
            reason=reason
        )


class MarkovAgent(TraceAgent):
    def __init__(self) -> None:
        super().__init__(stop_on_failure=True)

    @override
    def history(self) -> list[tuple[Tactic, bool]]:
        history_copy = super().history()
        return [history_copy[-1]] if history_copy else []


class ChoiceAgent(MarkovAgent):
    _all_choices: list[str]
    _check_index: int = 0

    def __init__(self, choices: list[str]):
        super().__init__()
        self._all_choices = choices

    def next(self, rdm: RocqDocManager) -> Tactic | GiveUp:
        if self.last_failed():
            self._check_index += 1
        else:
            self._check_index = 0

        if self._check_index >= len(self._all_choices):
            return self.give_up(
                FailureReason(ProofVerificationFailed())
            )

        return Tactic(self._all_choices[self._check_index])
