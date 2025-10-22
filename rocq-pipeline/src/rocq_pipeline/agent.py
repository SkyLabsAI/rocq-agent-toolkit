"""
Agents
"""

from dataclasses import dataclass
from typing import override, Self
from rocq_doc_manager import RocqDocManager

def close_proof(rdm: RocqDocManager):
    assert isinstance(rdm.run_command("Qed."), RocqDocManager.Resp)


@dataclass
class GiveUp(BaseException):
    message: str

@dataclass
class Tactic:
    tactic: str

class Agent:
    """A proof agent"""

    # TODO: tighten up the return type of [run]
    def run(self, rdm: RocqDocManager) -> GiveUp | bool | None:
        return GiveUp("not implemented")

class OneShotAgent(Agent):
    _tactic : str = "idtac"
    def __init__(self, tactic: str) -> None:
        self._tactic = tactic

    @override
    def run(self, rdm: RocqDocManager) -> GiveUp | bool | None:
        print("running oneshot")
        if isinstance(rdm.run_command(f"solve [ {self._tactic} ]."), RocqDocManager.Err):
            raise GiveUp(f"failed to solve the goal using: {self._tactic}")
        close_proof(rdm)
        return True

# NOTE: this agent does not support backtracking
class TraceAgent(Agent):
    def __init__(self, stop_on_failure: bool = False) -> None:
        self._stop_on_failure = stop_on_failure
        # Each element of [_history] is a tactic and a boolean indicating whether
        # the its application succeeded.
        self._history: list[tuple[Tactic, bool]] = list()
        print("Started agent!")

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
    def run(self, rdm: RocqDocManager) -> GiveUp | bool | None:
        should_trace = True
        def trace(f):
            if should_trace:
                print(f)

        # Start trying to verify the code
        while True:
            if self._stop_on_failure and self.last_failed():
                return GiveUp("i give up")

            if should_trace:
                goal = rdm.current_goal()
                trace(f"Current Goal:\r\n{goal}")

            tactic: Tactic | GiveUp = self.next(rdm)
            trace(f"Tactic: {tactic}")

            if isinstance(tactic, GiveUp):
                return tactic

            result = rdm.run_command(f"{tactic.tactic}.")
            if isinstance(result, rdm.Resp):
                self.update_history(tactic)
                if result.result['open_subgoals'] == 'No more goals.':
                    close_proof(rdm)
                    return True
            elif isinstance(result, rdm.Err):
                self.update_history(tactic, success=False)
                trace("failed")
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
        return self.Tactic(self._all_choices[self._check_index])
