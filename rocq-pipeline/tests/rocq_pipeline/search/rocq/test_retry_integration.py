"""
Integration tests for RocqRetryAction with generators and rectifiers.

These tests demonstrate the full flow of:
1. Generator produces tactics (potentially with errors)
2. RocqRetryAction attempts execution
3. On failure, rectifier is called with context
4. Corrected tactic is retried
"""

from typing import cast

import pytest
from rocq_doc_manager import RocqCursor
from rocq_pipeline.search.rocq.actions import RocqRetryCommandAction, RocqTacticAction

from .conftest import MockRocqCursor

pytestmark = pytest.mark.asyncio


class TestRocqRetryActionIntegration:
    """
    Integration tests showing how RocqRetryAction works with generators and rectifiers.
    """

    async def test_generator_with_rectifier_flow(self) -> None:
        """
        Simulates an LLM generator that produces a tactic with a typo,
        and a rectifier that fixes it based on the error message.
        """
        # Setup: cursor that fails on "autoo." but succeeds on "auto."
        cursor = MockRocqCursor(goal="∀ n : nat, n = n")
        cursor.set_failure("autoo.", "Unknown command: autoo")

        # Mock LLM generator that produces a tactic with a typo
        def mock_generator(goal: str) -> list[tuple[float, str]]:
            """Simulates LLM generating tactics - first one has a typo."""
            return [
                (0.9, "autoo."),  # Typo!
                (0.7, "reflexivity."),
            ]

        # Mock LLM rectifier that fixes the typo
        async def mock_rectifier(rc: RocqCursor, tactic: str, error: str) -> str | None:
            """
            Simulates LLM fixing a tactic based on error.
            In real usage, this would call the LLM with context.
            """
            if "Unknown command: autoo" in error:
                return "auto."  # Fixed!
            return None  # Can't fix

        # Create action with rectifier
        goal = await cursor.current_goal()
        assert goal is not None
        generated_tactics = mock_generator(goal)
        first_tactic = generated_tactics[0][1]  # "autoo."

        action = RocqRetryCommandAction(
            command=first_tactic,
            rectifier=mock_rectifier,
            max_retries=3,
        )

        # Execute - should fail first, then rectify and succeed
        result = await action.interact(cast(RocqCursor, cursor))

        # Verify the flow
        assert result is cursor
        assert cursor._commands == ["autoo.", "auto."]  # Tried typo, then fixed

    async def test_generator_strategy_simulation(self) -> None:
        """
        Simulates how GeneratorStrategy would use RocqRetryAction.

        In real code, GeneratorStrategy yields (prob, Action) pairs.
        Here we simulate that flow with retry-enabled actions.
        """
        cursor = MockRocqCursor(goal="n + 0 = n")
        cursor.set_failure("simpl;", "Syntax error: ';' instead of '.'")

        # Track rectifier calls for verification
        rectifier_calls: list[tuple[str, str, str]] = []

        async def tracking_rectifier(
            rc: RocqCursor, tactic: str, error: str
        ) -> str | None:
            goal = await cast(MockRocqCursor, rc).current_goal()
            assert goal is not None
            rectifier_calls.append((goal, tactic, error))
            if "Syntax error" in error and ";" in tactic:
                return tactic.replace(";", ".")  # Fix semicolon to period
            return None

        # Simulate what GeneratorStrategy.rollout() would produce
        def create_retry_action(command: str) -> RocqRetryCommandAction:
            return RocqRetryCommandAction(
                command=command,
                rectifier=tracking_rectifier,
                max_retries=2,
            )

        # Generator would yield these
        commands_from_llm = ["simpl;", "reflexivity."]

        # Try first tactic (has error, will be rectified)
        action1 = create_retry_action(commands_from_llm[0])
        result = await action1.interact(cast(RocqCursor, cursor))

        assert result is cursor
        assert cursor._commands == ["simpl;", "simpl."]  # Tried bad, then fixed

        # Verify rectifier was called with correct context
        assert len(rectifier_calls) == 1
        goal, tactic, error = rectifier_calls[0]
        assert goal == "n + 0 = n"
        assert tactic == "simpl;"
        assert "Syntax error" in error

    async def test_multiple_tactics_with_selective_retry(self) -> None:
        """
        Shows how to use retry for some tactics but not others.

        Useful when you want retry for LLM-generated tactics
        but not for mechanical/hardcoded tactics.
        """
        cursor = MockRocqCursor(goal="goal")
        cursor.set_failure("llm_tactic.", "Error from LLM tactic")

        async def always_fix(_rc: RocqCursor, _t: str, _e: str) -> str | None:
            return "fixed_tactic."

        # LLM tactic with retry
        llm_action = RocqRetryCommandAction(
            command="llm_tactic.",
            rectifier=always_fix,
            max_retries=2,
        )

        # Mechanical tactic without retry (use base RocqTacticAction)
        mechanical_action = RocqTacticAction("auto")

        # Execute LLM action (will retry and fix)
        await llm_action.interact(cast(RocqCursor, cursor))
        assert cursor._commands == ["llm_tactic.", "fixed_tactic."]

        # Execute mechanical action (no retry needed)
        cursor._commands.clear()
        await mechanical_action.interact(cast(RocqCursor, cursor))
        assert cursor._commands == ["auto."]

    async def test_rectifier_receives_updated_goal_context(self) -> None:
        """
        Verifies that rectifier receives the cursor to read the current goal.

        This is important because the goal may change between attempts if using
        checkpoint-based state (though not in this mock).
        """
        cursor = MockRocqCursor(goal="current goal state")
        cursor.set_failure("tactic1.", "First error")

        received_goals: list[str] = []

        async def goal_tracking_rectifier(
            rc: RocqCursor, tactic: str, error: str
        ) -> str | None:
            goal = await cast(MockRocqCursor, rc).current_goal()
            assert goal is not None
            received_goals.append(goal)
            return "tactic2."  # Fixed

        action = RocqRetryCommandAction(
            command="tactic1.",
            rectifier=goal_tracking_rectifier,
            max_retries=1,
        )

        await action.interact(cast(RocqCursor, cursor))

        # Rectifier should have received the goal from cursor
        assert received_goals == ["current goal state"]

    async def test_chain_of_corrections(self) -> None:
        """
        Tests a scenario where multiple corrections are needed.

        Simulates an LLM that gradually improves the tactic
        based on successive error messages.
        """
        cursor = MockRocqCursor(goal="complex goal")
        cursor.set_failure("step1.", "Missing argument")
        cursor.set_failure("step2.", "Type mismatch")
        cursor.set_failure("step3.", "Almost there")
        # "step4" will succeed

        correction_history: list[str] = []

        async def iterative_rectifier(
            _rc: RocqCursor, tactic: str, error: str
        ) -> str | None:
            correction_history.append(f"{tactic} -> error: {error}")

            # Simulate progressive fixing
            if tactic == "step1.":
                return "step2."
            elif tactic == "step2.":
                return "step3."
            elif tactic == "step3.":
                return "step4."
            return None

        action = RocqRetryCommandAction(
            command="step1.",
            rectifier=iterative_rectifier,
            max_retries=5,
        )

        result = await action.interact(cast(RocqCursor, cursor))

        assert result is cursor
        assert cursor._commands == ["step1.", "step2.", "step3.", "step4."]
        assert len(correction_history) == 3  # Three corrections made
