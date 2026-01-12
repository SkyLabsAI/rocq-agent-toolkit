from typing import override

from rocq_doc_manager import RocqCursor

from rocq_pipeline.agent.base import AgentBuilder
from rocq_pipeline.agent.proof.strategy_agent import StrategyAgent
from rocq_pipeline.search.action import Action
from rocq_pipeline.search.strategy import Strategy, empty_Rollout
from rocq_pipeline.task_runner import agent_main


class StepAction(Action[RocqCursor]):
    """
    This action uses `run_step` to evaluate the next command in the file.
    """

    def __init__(self, tac: str, ignore: int) -> None:
        super().__init__()
        self._key = tac
        self._ignore = ignore

    @override
    def key(self) -> str:
        return self._key

    @override
    def interact(self, state: RocqCursor) -> RocqCursor:
        for _ in range(0, self._ignore):
            if isinstance(state.run_step(), RocqCursor.Err):
                raise Action.Failed()
        next = state.doc_suffix()
        assert next
        assert next[0].text == self._key
        assert next[0].kind == "command"
        if isinstance(state.run_step(), RocqCursor.Err):
            raise Action.Failed()
        return state


class OracleStrategy(Strategy[RocqCursor]):
    """
    This strategy 'cheats' by looking at the document suffix to propose the next tactic.
    When the `doc_suffix` is hidden, this strategy will no longer work.
    """

    def rollout(
        self,
        state: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout[RocqCursor]:
        for count, cmd in enumerate(state.doc_suffix()):
            if cmd.kind != "command":
                continue
            if cmd.text.startswith("Proof"):
                continue
            return iter([(1.0, StepAction(tac, count)) for tac in [cmd.text]])
        return empty_Rollout()


class OracleAgent(StrategyAgent):
    """
    This agent 'cheats' by looking at the rest of the document to get
    a proof.
    """

    def __init__(self) -> None:
        super().__init__(OracleStrategy())


def main() -> bool:
    return agent_main(AgentBuilder.of_agent(OracleAgent))
