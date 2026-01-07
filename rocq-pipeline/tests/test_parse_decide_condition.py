import pytest
from rocq_pipeline.proof_state import BrickGoal


class TestParseDecideStatement:
    # 1. Happy Path: Standard Usage
    @pytest.mark.parametrize(
        "text, is_bool, expected_result",
        [
            (
                "if bool_decide (x > 5) then A else B",
                True,  # Use bool_decide=True
                "(x > 5)",
            ),
            (
                "if decide (y) then start() else stop()",
                False,  # Use bool_decide=False
                "(y)",
            ),
            ("if bool_decide b then X else Y", True, "b"),
        ],
    )
    def test_basic_parsing(self, text, is_bool, expected_result):
        # Call the static method
        result = BrickGoal.parse_decide_condition(text, bool_decide=is_bool)

        assert result is not None

        # Normalize whitespace of the results for comparison
        # (The function returns raw strings which might have leading/trailing spaces depending on input)
        cleaned_result = result.strip()
        assert cleaned_result == expected_result

    # 2. Multiline Support
    def test_multiline_content(self):
        text = """if bool_decide (
            complex_condition
        ) then
            do_something_long()
        else
            error()"""

        result = BrickGoal.parse_decide_condition(text, bool_decide=True)

        assert result is not None

        assert "complex_condition" in result

    # 3. Nested Parentheses (Valid)
    def test_nested_parentheses_valid(self):
        text = "if bool_decide (a + (b * c)) then (A + B) else C"
        result = BrickGoal.parse_decide_condition(text, bool_decide=True)

        assert result is not None
        assert result.strip() == "(a + (b * c))"

    # 4. Ambiguity Guard: "then" inside Condition
    def test_guard_fake_then_in_condition(self):
        # Should return None because the split causes unbalanced parens
        text = "if bool_decide (msg == 'then') then Print(B) else Print(C)"
        result = BrickGoal.parse_decide_condition(text, bool_decide=True)
        assert result == "(msg == 'then')"

    # 5. Ambiguity Guard: "else" inside Then-Block
    def test_guard_fake_else_in_then_block(self):
        # Should return None because the split causes unbalanced parens
        text = "if decide (x) then print('something else') else print('end')"
        result = BrickGoal.parse_decide_condition(text, bool_decide=False)
        assert result == "(x)"

    # 6. Syntax Error (Unbalanced inputs)
    def test_syntax_error_unbalanced_input(self):
        # Missing closing paren
        text = "if bool_decide (x > 5 then A else B"
        result = BrickGoal.parse_decide_condition(text, bool_decide=True)
        assert result is None

    # 7. Formatting Resilience
    def test_whitespace_resilience(self):
        text = "if    bool_decide\t(x)\n  then\n Y   else   Z"
        result = BrickGoal.parse_decide_condition(text, bool_decide=True)

        assert result is not None
        assert result == "(x)"

    # 8. Wrong Keyword Check
    def test_wrong_keyword_ignored(self):
        # If text uses 'decide' but we ask for 'bool_decide', it should fail (return None)
        text = "if decide (x) then A else B"
        result = BrickGoal.parse_decide_condition(text, bool_decide=True)
        assert result is None

    # 9. This shows a limitation of using regex matching for this purpose
    def test_else_with_rest(self):
        # If text uses 'decide' but we ask for 'bool_decide', it should fail (return None)
        text = "if decide (x) then A else B ** X"
        result = BrickGoal.parse_decide_condition(text, bool_decide=False)
        assert result == "(x)"
