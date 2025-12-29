from .one_shot import OneShotAgent


class AutoAgent(OneShotAgent, VERSION="1.0.0"):
    def __init__(self) -> None:
        super().__init__("auto")
