"""
Agents
"""

from dataclasses import dataclass
import pprint
from typing import override, Any, Self

from rocq_doc_manager import RocqDocManager

def close_proof(rdm: RocqDocManager):
    assert isinstance(rdm.run_command("Qed."), RocqDocManager.Resp)


@dataclass
class GiveUp:
    message: str

@dataclass
class Finished:
    message: str | None

@dataclass
class Tactic:
    tactic: str

class Agent:
    """A proof agent"""

    # TODO: tighten up the return type of [run]
    def run(self, rdm: RocqDocManager) -> Finished | GiveUp:
        return GiveUp("not implemented")

class OneShotAgent(Agent):
    _tactic : str = "idtac"
    def __init__(self, tactic: str) -> None:
        self._tactic = tactic

    @override
    def run(self, rdm: RocqDocManager) -> Finished | GiveUp:
        if isinstance(rdm.run_command(f"solve [ {self._tactic} ]."), RocqDocManager.Err):
            return GiveUp(f"failed to solve the goal using: {self._tactic}")
        return Finished("proof complete")


# NOTE: this agent does not support backtracking
class TraceAgent(Agent):
    """
    A next-tactic agent that can accumulate history to make the next decision.
    """
    def __init__(self, stop_on_failure: bool = False) -> None:
        self._stop_on_failure = stop_on_failure
        # Each element of [_history] is a tactic and a boolean indicating whether
        # the its application succeeded.
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

    @override
    def run(self, rdm: RocqDocManager) -> GiveUp | Finished:
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

            result = rdm.run_command(f"{tactic.tactic}.")
            if isinstance(result, rdm.Resp):
                self.update_history(tactic)
                if result.result['open_subgoals'] == 'No more goals.':
                    return Finished(None)
            elif isinstance(result, rdm.Err):
                self.update_history(tactic, success=False)
                trace("Failed", data=result)
                self.failed(result)

    def next(self, rdm : RocqDocManager) -> Tactic | GiveUp:
        """Invoked to get the next tactic to run.

        TODO: This needs to take a RocqDocManager so that it can query the goal, to
        extract additional information. Once it takes a RDM, it isn't clear if it should
        be in charge of committing the tactic or not.
        """
        return Tactic("auto")

    # TODO: determine how to better integrate this hook with [update_history]
    def failed(self, err: RocqDocManager.Err) -> None:
        """invoked if the last tactic failed"""
        pass

class MarkovAgent(TraceAgent):
    def __init__(self) -> None:
        super().__init__(stop_on_failure=True)

    @override
    def update_history(self, tactic: Tactic, success: bool = True) -> None:
        self._history = [(tactic, success)]

class ChoiceAgent(MarkovAgent):
    _all_choices: list[str]
    _check_index: int = 0
    _last_failed: bool = False

    def __init__(self, choices: list[str]):
        super().__init__()
        self._all_choices = choices

    def next(self, rdm: RocqDocManager) -> Tactic | GiveUp:
        if self.last_failed():
            self._check_index += 1
        else:
            self._check_index = 0
        if self._check_index >= len(self._all_choices):
            return GiveUp("i give up")
        return Tactic(self._all_choices[self._check_index])
