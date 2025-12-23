import logging
import re

import pytest
from rocq_doc_manager.rocq_cursor_protocol import RocqCursorProtocol


class Test_RocqCursorProtocol_ensure_args_endswith_period:
    """Test the ensure_args_endswith_period decorator."""

    def test_positional_only_parameter(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test that POSITIONAL_ONLY parameters are handled correctly."""

        @RocqCursorProtocol.ensure_args_endswith_period
        def func(text: str, /) -> str:
            return text

        with caplog.at_level(logging.WARNING):
            result = func("Check nat")
            assert result == "Check nat."
            assert "doesn't end with '.'" in caplog.text

        # Test with period already present
        caplog.clear()
        with caplog.at_level(logging.WARNING):
            result = func("Check nat.")
            assert result == "Check nat."
            assert "doesn't end with '.'" not in caplog.text

    def test_positional_or_keyword_positional(
        self, caplog: pytest.LogCaptureFixture
    ) -> None:
        """Test POSITIONAL_OR_KEYWORD parameter passed positionally."""

        @RocqCursorProtocol.ensure_args_endswith_period
        def func(text: str) -> str:
            return text

        with caplog.at_level(logging.WARNING):
            result = func("Check nat")
            assert result == "Check nat."
            assert "doesn't end with '.'" in caplog.text

    def test_positional_or_keyword_keyword(
        self, caplog: pytest.LogCaptureFixture
    ) -> None:
        """Test POSITIONAL_OR_KEYWORD parameter passed as keyword."""

        @RocqCursorProtocol.ensure_args_endswith_period
        def func(text: str) -> str:
            return text

        with caplog.at_level(logging.WARNING):
            result = func(text="Check nat")
            assert result == "Check nat."
            assert "doesn't end with '.'" in caplog.text

    def test_keyword_only_parameter(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test that KEYWORD_ONLY parameters are handled correctly."""

        @RocqCursorProtocol.ensure_args_endswith_period
        def func(*, text: str) -> str:
            return text

        with caplog.at_level(logging.WARNING):
            result = func(text="Check nat")
            assert result == "Check nat."
            assert "doesn't end with '.'" in caplog.text

    def test_multiple_parameters(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test multiple parameters being checked."""

        @RocqCursorProtocol.ensure_args_endswith_period(argnames={"text1", "text2"})
        def func(text1: str, text2: str) -> tuple[str, str]:
            return (text1, text2)

        with caplog.at_level(logging.WARNING):
            result = func("Check nat", "Check bool")
            assert result == ("Check nat.", "Check bool.")
            assert caplog.text.count("doesn't end with '.'") == 2

    def test_mixed_parameter_kinds(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test mixing POSITIONAL_ONLY, POSITIONAL_OR_KEYWORD, and KEYWORD_ONLY."""

        @RocqCursorProtocol.ensure_args_endswith_period(
            argnames={"pos_only", "pos_or_kw", "kw_only"},
        )
        def func(
            pos_only: str, /, pos_or_kw: str, *, kw_only: str
        ) -> tuple[str, str, str]:
            return (pos_only, pos_or_kw, kw_only)

        with caplog.at_level(logging.WARNING):
            result = func("Check nat", "Check bool", kw_only="Check unit")
            assert result == ("Check nat.", "Check bool.", "Check unit.")
            assert caplog.text.count("doesn't end with '.'") == 3

    def test_pos_or_kw_as_keyword_in_mixed(
        self, caplog: pytest.LogCaptureFixture
    ) -> None:
        """Test POSITIONAL_OR_KEYWORD passed as keyword in mixed signature."""

        @RocqCursorProtocol.ensure_args_endswith_period(argnames="pos_or_kw")
        def func(
            pos_only: str,
            /,
            pos_or_kw: str,
            *,
            kw_only: str,  # noqa: ARG001
        ) -> str:
            # pos_only and kw_only are required but not checked by decorator
            return pos_or_kw

        with caplog.at_level(logging.WARNING):
            result = func("ignored", pos_or_kw="Check nat", kw_only="ignored")
            assert result == "Check nat."
            assert "doesn't end with '.'" in caplog.text

    def test_var_positional_skipped(self) -> None:
        """Test that VAR_POSITIONAL (*args) parameters are skipped."""

        @RocqCursorProtocol.ensure_args_endswith_period
        def func(text: str, *args: str) -> tuple[str, tuple[str, ...]]:
            return (text, args)

        # Should work - text is processed, *args is ignored
        result = func("Check nat", "extra1", "extra2")
        assert result == ("Check nat.", ("extra1", "extra2"))

    def test_var_keyword_skipped(self) -> None:
        """Test that VAR_KEYWORD (**kwargs) parameters are skipped."""

        @RocqCursorProtocol.ensure_args_endswith_period
        def func(text: str, **kwargs: str) -> tuple[str, dict[str, str]]:
            return (text, kwargs)

        # Should work - text is processed, **kwargs is ignored
        result = func("Check nat", extra1="value1", extra2="value2")
        assert result == ("Check nat.", {"extra1": "value1", "extra2": "value2"})

    def test_var_positional_and_keyword_skipped(self) -> None:
        """Test that both VAR_POSITIONAL and VAR_KEYWORD are skipped."""

        @RocqCursorProtocol.ensure_args_endswith_period
        def func(
            text: str, *args: str, **kwargs: str
        ) -> tuple[str, tuple[str, ...], dict[str, str]]:
            return (text, args, kwargs)

        result = func("Check nat", "arg1", "arg2", kw1="val1", kw2="val2")
        assert result == (
            "Check nat.",
            ("arg1", "arg2"),
            {"kw1": "val1", "kw2": "val2"},
        )

    def test_invalid_parameter_name(self) -> None:
        """Test that invalid parameter names raise ValueError."""

        def func(text: str) -> str:
            return text

        with pytest.raises(ValueError, match="not found in parameters"):
            RocqCursorProtocol.ensure_args_endswith_period(
                argnames="nonexistent",
            )(func)

    def test_empty_argnames_with_text_ok(self) -> None:
        """Test that empty argnames raises ValueError."""

        def func(text: str) -> str:
            return text

        try:
            RocqCursorProtocol.ensure_args_endswith_period()(func)
        except Exception as e:
            pytest.fail(f"Unexpected failure: {e}")

    def test_parameter_already_has_period(
        self, caplog: pytest.LogCaptureFixture
    ) -> None:
        """Test that parameters already ending with period don't trigger warning."""

        @RocqCursorProtocol.ensure_args_endswith_period
        def func(text: str) -> str:
            return text

        with caplog.at_level(logging.WARNING):
            result = func("Check nat.")
            assert result == "Check nat."
            assert "doesn't end with '.'" not in caplog.text

    def test_ensure_text_endswith_period_helper(
        self, caplog: pytest.LogCaptureFixture
    ) -> None:
        """Test the ensure_text_endswith_period convenience decorator."""

        @RocqCursorProtocol.ensure_text_endswith_period
        def func(text: str) -> str:
            return text

        with caplog.at_level(logging.WARNING):
            result = func("Check nat")
            assert result == "Check nat."
            assert "doesn't end with '.'" in caplog.text

    def test_decorator_without_parens(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test decorator usage without parentheses (using ensure_text_endswith_period)."""

        @RocqCursorProtocol.ensure_text_endswith_period
        def func(text: str) -> str:
            return text

        with caplog.at_level(logging.WARNING):
            result = func("Check nat")
            assert result == "Check nat."
            assert "doesn't end with '.'" in caplog.text

    def test_decorator_with_parens_no_non_text_args_fails(self) -> None:
        """Test that decorator with parens but no args fails."""

        def func(cmd: str) -> str:
            return cmd

        with pytest.raises(
            ValueError,
            match=re.escape(
                "{'text'} not found in parameters of func: (cmd: str) -> str"
            ),
        ):
            RocqCursorProtocol.ensure_args_endswith_period()(func)

    def test_complex_signature(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test a complex function signature with all parameter kinds."""

        @RocqCursorProtocol.ensure_args_endswith_period(
            argnames={"pos_only", "pos_or_kw1", "pos_or_kw2", "kw_only"},
        )
        def func(
            pos_only: str,
            /,
            pos_or_kw1: str,
            pos_or_kw2: str = "default.",
            *,
            kw_only: str,
        ) -> tuple[str, str, str, str]:
            return (pos_only, pos_or_kw1, pos_or_kw2, kw_only)

        with caplog.at_level(logging.WARNING):
            # Test all positional
            result = func("Check nat", "Check bool", "Check unit", kw_only="Check list")
            assert result == ("Check nat.", "Check bool.", "Check unit.", "Check list.")
            assert caplog.text.count("doesn't end with '.'") == 4

        caplog.clear()
        with caplog.at_level(logging.WARNING):
            # Test mixed positional and keyword
            result = func(
                "Check nat", "Check bool", pos_or_kw2="Check unit", kw_only="Check list"
            )
            assert result == ("Check nat.", "Check bool.", "Check unit.", "Check list.")
            assert caplog.text.count("doesn't end with '.'") == 4

    def test_default_arguments_missing_period(self) -> None:
        """Test that default arguments work correctly."""

        with pytest.raises(ValueError, match="doesn't end with a '.'"):

            @RocqCursorProtocol.ensure_args_endswith_period
            def func(text: str = "Check nat") -> str:
                return text

    def test_multiple_parameters_some_checked(
        self, caplog: pytest.LogCaptureFixture
    ) -> None:
        """Test that only specified parameters are checked."""

        @RocqCursorProtocol.ensure_args_endswith_period(argnames="text1")
        def func(text1: str, text2: str, text3: str) -> tuple[str, str, str]:
            return (text1, text2, text3)

        with caplog.at_level(logging.WARNING):
            result = func("Check nat", "Check bool", "Check unit")
            assert result == ("Check nat.", "Check bool", "Check unit")
            # Only text1 should be checked
            assert caplog.text.count("doesn't end with '.'") == 1
            assert "text1" in caplog.text or "argument 'text1'" in caplog.text

    def test_function_metadata_preserved(self) -> None:
        """Test that functools.wraps preserves function metadata."""

        @RocqCursorProtocol.ensure_args_endswith_period
        def func(text: str) -> str:
            """A test function."""
            return text

        assert func.__name__ == "func"
        assert func.__doc__ == "A test function."

    def test_method_decorator(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test decorator on a method (with self parameter)."""

        class TestClass:
            @RocqCursorProtocol.ensure_args_endswith_period
            def method(self, text: str) -> str:
                return text

        obj = TestClass()
        with caplog.at_level(logging.WARNING):
            result = obj.method("Check nat")
            assert result == "Check nat."
            assert "doesn't end with '.'" in caplog.text

    def test_static_method_decorator(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test decorator on a static method."""

        class TestClass:
            @staticmethod
            @RocqCursorProtocol.ensure_args_endswith_period
            def static_method(text: str) -> str:
                return text

        with caplog.at_level(logging.WARNING):
            result = TestClass.static_method("Check nat")
            assert result == "Check nat."
            assert "doesn't end with '.'" in caplog.text

    def test_class_method_decorator(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test decorator on a class method."""

        class TestClass:
            @classmethod
            @RocqCursorProtocol.ensure_args_endswith_period
            def class_method(cls, text: str) -> str:
                return text

        with caplog.at_level(logging.WARNING):
            result = TestClass.class_method("Check nat")
            assert result == "Check nat."
            assert "doesn't end with '.'" in caplog.text
