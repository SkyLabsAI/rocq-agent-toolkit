from typing import override

from rocq_pipeline.agent.base import TacticApplication

from .trace import TraceAgent


class MarkovAgent(TraceAgent):
    def __init__(self) -> None:
        super().__init__(stop_on_failure=True)

    @override
    def history(self) -> list[TacticApplication]:
        history_copy = super().history()
        return [history_copy[-1]] if history_copy else []
