import pprint
from dataclasses import dataclass
from typing import Any, override

from rocq_doc_manager import RocqDocManager


def close_proof(rdm: RocqDocManager) -> None:
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
    def run(self, rdm: RocqDocManager) -> Finished | GiveUp:
        # Suppress unused argument warning for base class
        _ = rdm
        return GiveUp("not implemented")


class OneShotAgent(Agent):
    _tactic: str = "idtac"

    def __init__(self, tactic: str) -> None:
        self._tactic = tactic

    @override
    def run(self, rdm: RocqDocManager) -> Finished | GiveUp:
        if isinstance(rdm.run_command(f"solve [ {self._tactic} ]."), RocqDocManager.Err):
            return GiveUp(f"failed to solve the goal using: {self._tactic}")
        return Finished("proof complete")


# NOTE: this agent does not support backtracking
class TraceAgent(Agent):
    def __init__(self, stop_on_failure: bool = False) -> None:
        self._stop_on_failure = stop_on_failure
        # Each element of [_history] is a tactic and a boolean indicating whether
        # the its application succeeded.
        self._history: list[tuple[Tactic, bool]] = []

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

        def trace(msg: str, data: Any | None = None) -> None:
            if should_trace:
                print(msg)
                if data:
                    pprint.pprint(data, width=200)

        # Start trying to verify the code
        while True:
            if self._stop_on_failure and self.last_failed():
                return GiveUp("I give up")

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
        # Suppress unused argument warning for base class
        _ = rdm
        return GiveUp("not implemented")

    def failed(self, err: RocqDocManager.Err) -> None:
        # Base implementation does nothing - subclasses can override
        _ = err


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
            return GiveUp("I give up")
        return Tactic(self._all_choices[self._check_index])
