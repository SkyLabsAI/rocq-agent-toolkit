"""Tests for the ChoiceAgent functionality.

This module contains tests for the ChoiceAgent class and related functionality
in the rocq_pipeline package.
"""

import rocq_pipeline.task_runner
from rocq_pipeline.agent import ChoiceAgent

from .util import make_task


class SimpleTactics(ChoiceAgent):
    """A simple tactics agent for testing purposes.

    This class extends ChoiceAgent with a predefined set of Coq tactics
    for automated theorem proving.
    """

    def __init__(self) -> None:
        """Initialize the SimpleTactics agent with basic Coq tactics.

        Sets up the agent with a collection of common Coq tactics including
        trivial, tauto, auto, lia, and split.
        """
        super().__init__(["solve [ trivial ]", "tauto", "solve [ auto ]", "lia", "split"])


def test_choice_agent() -> None:
    """Test ChoiceAgent with a simple lemma.

    This test verifies that the ChoiceAgent can successfully process
    a simple lemma from the test_simple.v file using the SimpleTactics
    implementation.
    """
    result = rocq_pipeline.task_runner.main(
        SimpleTactics,
        ["--task-json", make_task("examples/theories/test_simple.v", "lemma:is_true")],
    )
    assert result
