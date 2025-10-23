"""Agents for automated theorem proving with Coq.

The Agent class provides a common interface for all derived agents.
The helper classes are:
- OneShotAgent: An agent that applies a single tactic to complete a proof.
- TraceAgent: An agent that can accumulate history to make the next decision.
- MarkovAgent: An agent that only remembers the last tactic applied.
- ChoiceAgent: An agent that tries tactics from a predefined list in order.

Note: currently, no agent supports backtracking and the proof state is exposed in
a relatively shallow way.
"""

from dataclasses import dataclass
import pprint
from typing import override, Any

from rocq_doc_manager import RocqDocManager  # type: ignore


def close_proof(rdm: RocqDocManager) -> None:
    """Close the current proof by running 'Qed.' command.

    Args:
        rdm: The RocqDocManager instance to run the command on.

    Raises:
        AssertionError: If the 'Qed.' command fails.
    """
    assert isinstance(rdm.run_command("Qed."), RocqDocManager.Resp)


@dataclass
class GiveUp:
    """Represents a failure state when an agent cannot complete a proof.

    Attributes:
        message: A description of why the agent gave up.
    """

    message: str


@dataclass
class Finished:
    """Represents a successful completion of a proof.

    Attributes:
        message: An optional completion message, or None if no message.
    """

    message: str | None


@dataclass
class Tactic:
    """Represents a Coq tactic to be applied.

    Attributes:
        tactic: The tactic string to execute.
    """

    tactic: str


class Agent:
    """Base class for Rocq agents.

    A Rocq agent is reponsible for completing tasks within a Rocq document,
    for example, proving a theorem. The agent is given a RocqDocManager and
    is expected to return a Finished or GiveUp.
    """

    def run(self, rdm: RocqDocManager) -> Finished | GiveUp:
        """Run the agent to attempt to complete the task.

        Args:
            rdm: The RocqDocManager instance containing the document.

        Returns:
            Either Finished if the task is completed, or GiveUp if the agent
            cannot complete the task.
        """
        # Suppress unused argument warning for base class
        _ = rdm
        return GiveUp("not implemented")


class OneShotAgent(Agent):
    """An agent that applies a single tactic to complete a proof.

    This agent attempts to solve the current goal using a single specified tactic.
    If the tactic fails, the agent gives up immediately.
    """

    _tactic: str = "idtac"

    def __init__(self, tactic: str) -> None:
        """Initialize the one-shot agent with a specific tactic.

        Args:
            tactic: The Coq tactic to apply for proof completion.
        """
        self._tactic = tactic

    @override
    def run(self, rdm: RocqDocManager) -> Finished | GiveUp:
        """Run the agent by applying the specified tactic.

        Args:
            rdm: The RocqDocManager instance containing the proof context.

        Returns:
            Finished if the tactic succeeds, GiveUp if it fails.
        """
        if isinstance(
            rdm.run_command(f"solve [ {self._tactic} ]."), RocqDocManager.Err
        ):
            return GiveUp(f"failed to solve the goal using: {self._tactic}")
        return Finished("proof complete")


# NOTE: this agent does not support backtracking
class TraceAgent(Agent):
    """A next-tactic agent that can accumulate history to make the next decision.

    This agent maintains a history of applied tactics and their success/failure
    status, which can be used to inform future tactic selection. Note that this
    agent does not support backtracking - once a tactic is applied, it cannot be undone.
    """

    def __init__(self, stop_on_failure: bool = False) -> None:
        """Initialize the trace agent.

        Args:
            stop_on_failure: If True, the agent will give up immediately after
                the first failed tactic. If False, it will continue trying.
        """
        self._stop_on_failure = stop_on_failure
        # Each element of [_history] is a tactic and a boolean indicating whether
        # the its application succeeded.
        self._history: list[tuple[Tactic, bool]] = []

    def last_failed(self) -> bool:
        """Check if the last applied tactic failed.

        Returns:
            True if the last tactic failed, False if it succeeded or if no tactics
            have been applied yet.
        """
        if not self._history:
            return False

        return self._history[-1][1]

    def update_history(self, tactic: Tactic, success: bool = True) -> None:
        """Add a tactic and its result to the history.

        Args:
            tactic: The tactic that was applied.
            success: Whether the tactic succeeded (default: True).
        """
        self._history.append((tactic, success))

    def history(self) -> list[tuple[Tactic, bool]]:
        """Get a copy of the tactic history.

        Returns:
            A shallow copy of the history list containing (tactic, success) tuples.
        """
        # Note: return a shallow copy of the history
        return self._history[:]

    @override
    def run(self, rdm: RocqDocManager) -> GiveUp | Finished:
        """Run the trace agent to attempt proof completion.

        This method runs in a loop, repeatedly selecting and applying tactics
        until either the proof is completed or the agent gives up.

        Args:
            rdm: The RocqDocManager instance containing the proof context.

        Returns:
            Either Finished if the proof is completed, or GiveUp if the agent
            cannot complete the proof.
        """
        should_trace = True

        def trace(msg, data: Any | None = None):
            if should_trace:
                print(msg)
                if data:
                    pprint.pprint(data, width=200)

        # Start trying to verify the code
        while True:
            if self._stop_on_failure and self.last_failed():
                return GiveUp("i give up")

            if should_trace:
                goal = rdm.current_goal()
                trace("Current Goal:", data=goal)

            tactic: Tactic | GiveUp = self.next(rdm)
            trace("Tactic:", data=tactic)

            if isinstance(tactic, GiveUp):
                return tactic

            result = rdm.run_command(f"{tactic.tactic}.")  # pylint: disable=no-member
            if isinstance(result, rdm.Resp):
                self.update_history(tactic)
                if result.result["open_subgoals"] == "No more goals.":
                    return Finished(None)
            elif isinstance(result, rdm.Err):
                self.update_history(tactic, success=False)
                trace("Failed", data=result)
                self.failed(result)

    def next(self, rdm: RocqDocManager) -> Tactic | GiveUp:
        """Get the next tactic to apply.

        This method should be overridden by subclasses to implement specific
        tactic selection strategies.

        Args:
            rdm: The RocqDocManager instance containing the proof context.

        Returns:
            Either a Tactic to apply next, or GiveUp if no suitable tactic
            can be determined.

        TODO: This needs to take a RocqDocManager so that it can query the goal, to
        extract additional information. Once it takes a RDM, it isn't clear if it should
        be in charge of committing the tactic or not.
        """
        # Suppress unused argument warning for base class
        _ = rdm
        return GiveUp("not implemented")

    def failed(self, err: RocqDocManager.Err) -> None:
        """Handle the case when the last tactic failed.

        This method is called when a tactic application fails. Subclasses can
        override this to implement custom failure handling logic.

        Args:
            err: The error that occurred when applying the tactic.
        """
        # Base implementation does nothing - subclasses can override
        _ = err


class MarkovAgent(TraceAgent):
    """A Markov agent that only remembers the last tactic applied.

    This agent maintains a memory of only the most recent tactic and its result,
    implementing a Markov property where the next decision depends only on the
    current state, not the full history.
    """

    def __init__(self) -> None:
        """Initialize the Markov agent with stop-on-failure enabled."""
        super().__init__(stop_on_failure=True)

    @override
    def update_history(self, tactic: Tactic, success: bool = True) -> None:
        """Update history to only keep the most recent tactic.

        Args:
            tactic: The tactic that was applied.
            success: Whether the tactic succeeded.
        """
        self._history = [(tactic, success)]


class ChoiceAgent(MarkovAgent):
    """An agent that tries tactics from a predefined list in order.

    This agent maintains a list of tactics to try and attempts them in sequence.
    If a tactic fails, it moves to the next one. If all tactics fail, it gives up.
    """

    _all_choices: list[str]
    _check_index: int = 0
    _last_failed: bool = False

    def __init__(self, choices: list[str]):
        """Initialize the choice agent with a list of tactics to try.

        Args:
            choices: A list of tactic strings to try in order.
        """
        super().__init__()
        self._all_choices = choices

    def next(self, rdm: RocqDocManager) -> Tactic | GiveUp:
        """Get the next tactic from the predefined list.

        Args:
            rdm: The RocqDocManager instance containing the proof context.

        Returns:
            The next tactic to try, or GiveUp if all tactics have been exhausted.
        """
        if self.last_failed():
            self._check_index += 1
        else:
            self._check_index = 0
        if self._check_index >= len(self._all_choices):
            return GiveUp("i give up")
        return Tactic(self._all_choices[self._check_index])
