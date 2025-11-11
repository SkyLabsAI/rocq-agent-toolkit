from argparse import ArgumentParser, Namespace
from typing import override

from rocq_pipeline.agent import OneShotAgent


class AutoAgent(OneShotAgent):
    def __init__(self) -> None:
        super().__init__("auto")

    @staticmethod
    def arg_parser(args: ArgumentParser) -> None:
        pass

    @override
    @staticmethod
    def build(prompt: str | None, args: Namespace) -> "AutoAgent":
        return AutoAgent()
