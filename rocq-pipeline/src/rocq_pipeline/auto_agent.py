from typing import override
from rocq_pipeline.agent import MarkovAgent, GiveUp, Tactic
from rocq_doc_manager import RocqDocManager

class AutoAgent(MarkovAgent):
    @override
    def next(self, rdm: RocqDocManager):
        return Tactic("by auto")

    @override
    def failed(self, err: RocqDocManager.Err):
        raise GiveUp("`by auto` did not solve the goal")
