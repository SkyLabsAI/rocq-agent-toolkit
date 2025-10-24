from rocq_pipeline.agent import OneShotAgent


class AutoAgent(OneShotAgent):
    def __init__(self) -> None:
        super().__init__("auto")
