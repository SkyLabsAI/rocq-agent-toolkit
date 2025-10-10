"""
Agents
"""

from dataclasses import dataclass
from typing import override
from rocq_doc_manager import RocqDocManager

def close_proof(rdm: RocqDocManager):
    assert isinstance(rdm.run_command("Qed."), RocqDocManager.Resp)


@dataclass
class GiveUp(BaseException):
    message: str

class Agent:
    """A proof agent"""
    def run(self, rdm: RocqDocManager):
        return GiveUp("not implemented")

class OneShotAgent(Agent):
    _tactic : str = "idtac"
    def __init__(self, tactic: str):
        self._tactic = tactic

    @override
    def run(self, rdm: RocqDocManager):
        print("running oneshot")
        if isinstance(rdm.run_command(f"solve [ {self._tactic} ]."), RocqDocManager.Err):
            raise GiveUp(f"failed to solve the goal using: {self._tactic}")
        close_proof(rdm)
        return True

class MarkovAgent(Agent):
    _last_failed : bool = False
    def __init__(self):
        print("Started agent!")

    @dataclass
    class Tactic:
        tactic: str

    @override
    def run(self, rdm: RocqDocManager):
        should_trace = True
        def trace(f):
            if should_trace:
                print(f)

        # Start trying to verify the code
        while True:
            if should_trace:
                goal = rdm.current_goal()
                trace(f"Current Goal:\r\n{goal}")
            print("1")
            tactic = self.next(rdm)
            trace(f"Tactic: {tactic}")
            if isinstance(tactic, GiveUp):
                return tactic
            result = rdm.run_command(f"{tactic.tactic}.")
            if isinstance(result, rdm.Resp):
                if result.result['open_subgoals'] == 'No more goals.':
                    close_proof(rdm)
                    return True
            elif isinstance(result, rdm.Err):
                trace("failed")
                self.failed(result)

    def next(self, rdm : RocqDocManager): # MarkovAgent.Tactic
        """Invoked to get the next tactic to run.

        TODO: This needs to take a RocqDocManager so that it can query the goal, to
        extract additional information. Once it takes a RDM, it isn't clear if it should
        be in charge of committing the tactic or not.
        """
        if self._last_failed:
            return GiveUp("i give up")
        return MarkovAgent.Tactic("auto")

    def failed(self, err: RocqDocManager.Err):
        """invoked if the last tactic failed"""
        self._last_failed = True

class ChoiceAgent(MarkovAgent):
    _all_choices: list[str]
    _check_index: int = 0
    _last_failed: bool = False

    def __init__(self, choices: list[str]):
        super().__init__()
        self._all_choices = choices

    def next(self, rdm: RocqDocManager) -> MarkovAgent.Tactic | GiveUp:
        if self._last_failed:
            self._check_index += 1
        else:
            self._check_index = 0
        self._last_failed = False
        if self._check_index >= len(self._all_choices):
            return GiveUp("i give up")
        return self.Tactic(self._all_choices[self._check_index])

    def failed(self, err: RocqDocManager.Err):
        self._last_failed = True
