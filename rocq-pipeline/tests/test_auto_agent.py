"""Tests for the AutoAgent functionality.

This module contains tests for the AutoAgent class and related functionality
in the rocq_pipeline package.
"""

import rocq_pipeline.task_runner
from rocq_pipeline.agent import Agent
from rocq_pipeline.auto_agent import AutoAgent

from .util import make_task


def test_auto() -> None:
    """Test AutoAgent with a simple lemma.

    This test verifies that the AutoAgent can successfully process
    a simple lemma from the test_simple.v file.
    """
    result = rocq_pipeline.task_runner.main(
        AutoAgent,
        ["--task-json", make_task("examples/theories/test_simple.v", "lemma:is_true")],
    )
    assert result


def test_failure() -> None:
    """Test Agent with a simple lemma.

    This test verifies that the base Agent can successfully process
    a simple lemma from the test_simple.v file.
    """
    result = rocq_pipeline.task_runner.main(
        Agent,
        ["--task-json", make_task("examples/theories/test_simple.v", "lemma:is_true")],
    )
    assert result
