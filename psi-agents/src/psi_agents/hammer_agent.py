
from rocq_pipeline.agent import OneShotAgent

class HammerAgent(OneShotAgent):
    """Invoke the SkyLabs AI 'hammer' tactic"""
    def __init__(self):
        super().__init__("verify_spec; go")
