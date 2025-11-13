from rocq_pipeline.agent import Agent, AgentBuilder, OneShotAgent


class OneShotBuilder(AgentBuilder):
    def __init__(self) -> None:
        self._tactic:str|None = None

    def add_args(self, args:list[str]) -> None:
        if len(args) == 1:
            self._tactic = args[0]
        elif len(args) == 0:
            print("Missing tactic argument")
        else:
            print("Too many tactics given")

    def __call__(self, prompt:str|None=None) -> Agent:
        if self._tactic is None:
            print("Missing tactic argument")
            raise ValueError("Missing tactic argument")
        return OneShotAgent(self._tactic)

default = AgentBuilder.of_agent(Agent)
one_shot = OneShotBuilder()
