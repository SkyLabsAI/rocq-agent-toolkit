from typing import override
from rocq_pipeline.agent import GiveUp, OneShotAgent, Tactic
from rocq_doc_manager import RocqDocManager

class AutoAgent(OneShotAgent):
    def __init__(self):
        super().__init__("auto")
