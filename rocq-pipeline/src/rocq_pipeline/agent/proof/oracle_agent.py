from typing import override

from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

from rocq_pipeline.agent.base import AgentBuilder, ProofAgent, TaskResult
from rocq_pipeline.task_runner import agent_main


class OracleAgent(ProofAgent):
    """
    This agent 'cheats' by looking at the rest of the document to get
    a proof.
    """

    def __init__(self) -> None:
        super().__init__(unset_ssr_idents=False, reset_default_goal_selector=False)

    @override
    async def run(self, rc: RocqCursor) -> TaskResult:
        while await self.current_proof_state(rc):
            result = await rc.run_step()
            if isinstance(result, rdm_api.Err):
                suffix = await rc.doc_suffix()
                try:
                    last = suffix.pop()
                    return await self.give_up(
                        rc, f"Failed to run command '{last.text}'"
                    )
                except IndexError:
                    return await self.give_up(rc, "No commands left in the file")
            # Otherwise we inserted blanks or a command that succeeded.

        return await self.finished(rc)


def main() -> bool:
    return agent_main(AgentBuilder.of_agent(OracleAgent))
