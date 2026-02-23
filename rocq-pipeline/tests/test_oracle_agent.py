import tempfile

import rocq_pipeline.task_runner
from rocq_pipeline.agent import AgentBuilder
from rocq_pipeline.agent.proof.oracle_agent import OracleAgent

from .util import make_task_str


def test_oracle_agent() -> None:
    with tempfile.TemporaryDirectory() as temp_dir:
        result = rocq_pipeline.task_runner.agent_main(
            AgentBuilder.of_agent(OracleAgent),
            [
                "--task-json",
                make_task_str("examples/theories/test_simple.v", None, "Lemma:is_true"),
                "--output-dir",
                temp_dir,
            ],
        )
    assert result
