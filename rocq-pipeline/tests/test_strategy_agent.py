"""Integration test for StrategyAgent with task_runner framework.

This test verifies that StrategyAgent properly captures the "doc_interaction"
side-effect in the produced task result.
"""

import json
import tempfile
from pathlib import Path

import rocq_pipeline.task_runner
from rocq_pipeline.agent import AgentBuilder
from rocq_pipeline.agent.proof.strategy_agent import StrategyAgent
from rocq_pipeline.schema import task_output
from rocq_pipeline.search.rocq.strategies import FirstTacticStrategy
from rocq_pipeline.search.strategy import Strategy

from .util import make_task_str


class StrategyAgentBuilder(AgentBuilder):
    """Builder for StrategyAgent with a fixed strategy."""

    def __init__(self, strategy: Strategy) -> None:
        super().__init__()
        self._strategy = strategy

    def __call__(self, prompt: str | None = None) -> StrategyAgent:
        return StrategyAgent(strategy=self._strategy)


def test_strategy_agent_doc_interaction() -> None:
    """Test that StrategyAgent captures doc_interaction in side_effects."""
    # Create a simple strategy that uses "auto." tactic
    # FirstTacticStrategy takes a list of (probability, tactic) pairs
    strategy = FirstTacticStrategy([(1.0, "auto.")])

    # Create an AgentBuilder for StrategyAgent with the strategy
    agent_builder = StrategyAgentBuilder(strategy)

    with tempfile.TemporaryDirectory() as temp_dir:
        output_dir = Path(temp_dir)

        # Run the agent on the test.v file with the test_true lemma
        # The file path is relative to the rocq-pipeline directory
        result = rocq_pipeline.task_runner.agent_main(
            agent_builder,
            [
                "--task-json",
                make_task_str("tests/test.v", "Lemma:test_true"),
                "--output-dir",
                str(output_dir),
            ],
        )

        # Verify the run succeeded
        assert result, "agent_main should return True"

        # Find the output JSONL file
        result_files = list(output_dir.glob("*_results_*.jsonl"))
        assert len(result_files) == 1, (
            f"Expected 1 result file, found {len(result_files)}"
        )
        result_file = result_files[0]

        # Read and parse the result
        with open(result_file, encoding="utf-8") as f:
            lines = [line for line in f if line.strip()]
            assert len(lines) == 2, f"Expected 2 result lines, found {len(lines)}"

            run_header_json = json.loads(lines[0])
            run_header_obj = task_output.RunHeader.from_json(run_header_json)
            assert run_header_obj.type == "run", (
                f"Expected run header, got type={run_header_obj.type}"
            )

            task_output_json = json.loads(lines[1])
            task_output_obj = task_output.TaskOutput.from_json(task_output_json)
            assert task_output_obj.type == "task", (
                f"Expected task output, got type={task_output_obj.type}"
            )

        # Verify the task succeeded
        assert str(task_output_obj.status.value.kind) == "Success", (
            f"Expected Success, got {task_output_obj.status.value.kind}"
        )

        # Verify results is a dict with side_effects
        assert isinstance(task_output_obj.results, dict), (
            f"Expected results to be a dict, got {type(task_output_obj.results)}"
        )

        # Verify side_effects exists
        assert "side_effects" in task_output_obj.results, (
            "Expected 'side_effects' key in results"
        )

        side_effects = task_output_obj.results["side_effects"]
        assert isinstance(side_effects, dict), (
            f"Expected side_effects to be a dict, got {type(side_effects)}"
        )

        # Verify doc_interaction exists in side_effects
        assert "doc_interaction" in side_effects, (
            "Expected 'doc_interaction' key in side_effects"
        )

        doc_interaction = side_effects["doc_interaction"]
        assert isinstance(doc_interaction, str), (
            f"Expected doc_interaction to be a string, got {type(doc_interaction)}"
        )

        # Verify doc_interaction contains the tactic we applied
        assert "auto" in doc_interaction.lower(), (
            f"Expected 'auto' in doc_interaction, got: {doc_interaction}"
        )

        # Verify doc_interaction is non-empty
        assert len(doc_interaction) > 0, "Expected doc_interaction to be non-empty"
