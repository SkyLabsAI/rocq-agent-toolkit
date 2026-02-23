from typing import Protocol, override, runtime_checkable

from rocq_doc_manager import RocqCursor
from rocq_doc_manager.rocq_doc_manager import rdm_api
from rocq_pipeline.agent.base import Agent, AgentBuilder, TaskResult


@runtime_checkable
class Interaction(Protocol):
    async def run(self, rc: RocqCursor) -> None: ...


class InsertCommandInteraction(Interaction):
    def __init__(self, cmd: str, assert_succeeds: bool = True):
        self._command = cmd
        self._assert_succeeds = assert_succeeds

    async def run(self, rc: RocqCursor) -> None:
        result = await rc.insert_command(self._command)
        print(result)
        if self._assert_succeeds:
            assert isinstance(result, rdm_api.CommandData)


class PuppetAgent(Agent):
    def __init__(self, interactions: list[Interaction]):
        super().__init__()

        self._interactions = interactions

    @override
    async def run(self, rc: RocqCursor) -> TaskResult:
        for i in self._interactions:
            await i.run(rc)
        return TaskResult.give_up("completed interactions")


class PuppetBuilder(AgentBuilder):
    def __init__(self):
        super().__init__(PuppetAgent)
        self._interactions: list[Interaction] = []

    def __call__(self, prompt: str | None = None) -> Agent:
        return PuppetAgent(self._interactions)

    def add_args(self, args: list[str]) -> None:
        self._interactions = [InsertCommandInteraction(cmd) for cmd in args]


puppet_builder = PuppetBuilder()
