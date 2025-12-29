"""
Integration tests for RocqRetryAction with generators and rectifiers.

These tests demonstrate the full flow of:
1. Generator produces tactics (potentially with errors)
2. RocqRetryAction attempts execution
3. On failure, rectifier is called with context
4. Corrected tactic is retried
"""

from rocq_pipeline.search.rocq.actions import RocqRetryAction, RocqTacticAction

from .conftest import MockRocqCursor


class TestRocqRetryActionIntegration:
    """
    Integration tests showing how RocqRetryAction works with generators and rectifiers.
    """

    def test_generator_with_rectifier_flow(self) -> None:
        """
        Simulates an LLM generator that produces a tactic with a typo,
        and a rectifier that fixes it based on the error message.
        """
        # Setup: cursor that fails on "autoo." but succeeds on "auto."
        cursor = MockRocqCursor(goal="∀ n : nat, n = n")
        cursor.set_failure("autoo.", "Unknown tactic: autoo")

        # Mock LLM generator that produces a tactic with a typo
        def mock_generator(goal: str) -> list[tuple[float, str]]:
            """Simulates LLM generating tactics - first one has a typo."""
            return [
                (0.9, "autoo."),  # Typo!
                (0.7, "reflexivity."),
            ]

        # Mock LLM rectifier that fixes the typo
        def mock_rectifier(goal: str, tactic: str, error: str) -> str | None:
            """
            Simulates LLM fixing a tactic based on error.
            In real usage, this would call the LLM with context.
            """
            if "Unknown tactic: autoo" in error:
                return "auto."  # Fixed!
            return None  # Can't fix

        # Create action with rectifier
        generated_tactics = mock_generator(cursor.current_goal())
        first_tactic = generated_tactics[0][1]  # "autoo."

        action = RocqRetryAction(
            tactic=first_tactic,
            rectifier=mock_rectifier,
            max_retries=3,
        )

        # Execute - should fail first, then rectify and succeed
        result = action.interact(cursor)

        # Verify the flow
        assert result is cursor
        assert cursor._commands == ["autoo.", "auto."]  # Tried typo, then fixed

    def test_generator_strategy_simulation(self) -> None:
        """
        Simulates how GeneratorStrategy would use RocqRetryAction.

        In real code, GeneratorStrategy yields (prob, Action) pairs.
        Here we simulate that flow with retry-enabled actions.
        """
        cursor = MockRocqCursor(goal="n + 0 = n")
        cursor.set_failure("simpl;", "Syntax error: ';' instead of '.'")

        # Track rectifier calls for verification
        rectifier_calls: list[tuple[str, str, str]] = []

        def tracking_rectifier(goal: str, tactic: str, error: str) -> str | None:
            rectifier_calls.append((goal, tactic, error))
            if "Syntax error" in error and ";" in tactic:
                return tactic.replace(";", ".")  # Fix semicolon to period
            return None

        # Simulate what GeneratorStrategy.rollout() would produce
        def create_retry_action(tactic: str) -> RocqRetryAction:
            return RocqRetryAction(
                tactic=tactic,
                rectifier=tracking_rectifier,
                max_retries=2,
            )

        # Generator would yield these
        tactics_from_llm = ["simpl;", "reflexivity."]

        # Try first tactic (has error, will be rectified)
        action1 = create_retry_action(tactics_from_llm[0])
        result = action1.interact(cursor)

        assert result is cursor
        assert cursor._commands == ["simpl;", "simpl."]  # Tried bad, then fixed

        # Verify rectifier was called with correct context
        assert len(rectifier_calls) == 1
        goal, tactic, error = rectifier_calls[0]
        assert goal == "n + 0 = n"
        assert tactic == "simpl;"
        assert "Syntax error" in error

    def test_multiple_tactics_with_selective_retry(self) -> None:
        """
        Shows how to use retry for some tactics but not others.

        Useful when you want retry for LLM-generated tactics
        but not for mechanical/hardcoded tactics.
        """
        cursor = MockRocqCursor(goal="goal")
        cursor.set_failure("llm_tactic", "Error from LLM tactic")

        # LLM tactic with retry
        llm_action = RocqRetryAction(
            tactic="llm_tactic",
            rectifier=lambda g, t, e: "fixed_tactic",
            max_retries=2,
        )

        # Mechanical tactic without retry (use base RocqTacticAction)
        mechanical_action = RocqTacticAction("auto.")

        # Execute LLM action (will retry and fix)
        llm_action.interact(cursor)
        assert cursor._commands == ["llm_tactic", "fixed_tactic"]

        # Execute mechanical action (no retry needed)
        cursor._commands.clear()
        mechanical_action.interact(cursor)
        assert cursor._commands == ["auto."]

    def test_rectifier_receives_updated_goal_context(self) -> None:
        """
        Verifies that rectifier receives the current goal from cursor.

        This is important because the goal may change between attempts
        if using checkpoint-based state (though not in this mock).
        """
        cursor = MockRocqCursor(goal="current goal state")
        cursor.set_failure("tactic1", "First error")

        received_goals: list[str] = []

        def goal_tracking_rectifier(goal: str, tactic: str, error: str) -> str | None:
            received_goals.append(goal)
            return "tactic2"  # Fixed

        action = RocqRetryAction(
            tactic="tactic1",
            rectifier=goal_tracking_rectifier,
            max_retries=1,
        )

        action.interact(cursor)

        # Rectifier should have received the goal from cursor
        assert received_goals == ["current goal state"]

    def test_chain_of_corrections(self) -> None:
        """
        Tests a scenario where multiple corrections are needed.

        Simulates an LLM that gradually improves the tactic
        based on successive error messages.
        """
        cursor = MockRocqCursor(goal="complex goal")
        cursor.set_failure("step1", "Missing argument")
        cursor.set_failure("step2", "Type mismatch")
        cursor.set_failure("step3", "Almost there")
        # "step4" will succeed

        correction_history: list[str] = []

        def iterative_rectifier(goal: str, tactic: str, error: str) -> str | None:
            correction_history.append(f"{tactic} -> error: {error}")

            # Simulate progressive fixing
            if tactic == "step1":
                return "step2"
            elif tactic == "step2":
                return "step3"
            elif tactic == "step3":
                return "step4"
            return None

        action = RocqRetryAction(
            tactic="step1",
            rectifier=iterative_rectifier,
            max_retries=5,
        )

        result = action.interact(cursor)

        assert result is cursor
        assert cursor._commands == ["step1", "step2", "step3", "step4"]
        assert len(correction_history) == 3  # Three corrections made

