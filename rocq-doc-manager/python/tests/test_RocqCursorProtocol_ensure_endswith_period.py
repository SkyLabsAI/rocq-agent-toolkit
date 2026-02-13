import logging
import re

import pytest
from rocq_doc_manager.rocq_cursor_protocol import RocqCursor


class Test_RocqCursorProtocol_ensure_args_endswith_period:
    """Test the ensure_endswith_period decorator."""

    def test_positional_only_parameter(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test that POSITIONAL_ONLY parameters are handled correctly."""

        @RocqCursor.ensure_endswith_period(argnames="text")
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

        @RocqCursor.ensure_endswith_period(argnames="text")
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

        @RocqCursor.ensure_endswith_period(argnames="text")
        def func(text: str) -> str:
            return text

        with caplog.at_level(logging.WARNING):
            result = func(text="Check nat")
            assert result == "Check nat."
            assert "doesn't end with '.'" in caplog.text

    def test_keyword_only_parameter(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test that KEYWORD_ONLY parameters are handled correctly."""

        @RocqCursor.ensure_endswith_period(argnames="text")
        def func(*, text: str) -> str:
            return text

        with caplog.at_level(logging.WARNING):
            result = func(text="Check nat")
            assert result == "Check nat."
            assert "doesn't end with '.'" in caplog.text

    def test_multiple_parameters(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test multiple parameters being checked."""

        @RocqCursor.ensure_endswith_period(argnames={"text1", "text2"})
        def func(text1: str, text2: str) -> tuple[str, str]:
            return (text1, text2)

        with caplog.at_level(logging.WARNING):
            result = func("Check nat", "Check bool")
            assert result == ("Check nat.", "Check bool.")
            assert caplog.text.count("doesn't end with '.'") == 2

    def test_mixed_parameter_kinds(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test mixing POSITIONAL_ONLY, POSITIONAL_OR_KEYWORD, and KEYWORD_ONLY."""

        @RocqCursor.ensure_endswith_period(
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

        @RocqCursor.ensure_endswith_period(argnames="pos_or_kw")
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

        @RocqCursor.ensure_endswith_period(argnames="text")
        def func(text: str, *args: str) -> tuple[str, tuple[str, ...]]:
            return (text, args)

        # Should work - text is processed, *args is ignored
        result = func("Check nat", "extra1", "extra2")
        assert result == ("Check nat.", ("extra1", "extra2"))

    def test_var_keyword_skipped(self) -> None:
        """Test that VAR_KEYWORD (**kwargs) parameters are skipped."""

        @RocqCursor.ensure_endswith_period(argnames="text")
        def func(text: str, **kwargs: str) -> tuple[str, dict[str, str]]:
            return (text, kwargs)

        # Should work - text is processed, **kwargs is ignored
        result = func("Check nat", extra1="value1", extra2="value2")
        assert result == ("Check nat.", {"extra1": "value1", "extra2": "value2"})

    def test_var_positional_and_keyword_skipped(self) -> None:
        """Test that both VAR_POSITIONAL and VAR_KEYWORD are skipped."""

        @RocqCursor.ensure_endswith_period(argnames="text")
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
            RocqCursor.ensure_endswith_period(
                argnames="nonexistent",
            )(func)

    def test_empty_argnames_with_text_ok(self) -> None:
        """Test that empty argnames raises ValueError."""

        def func(text: str) -> str:
            return text

        try:
            RocqCursor.ensure_endswith_period(argnames="text")(func)
        except Exception as e:
            pytest.fail(f"Unexpected failure: {e}")

    def test_parameter_already_has_period(
        self, caplog: pytest.LogCaptureFixture
    ) -> None:
        """Test that parameters already ending with period don't trigger warning."""

        @RocqCursor.ensure_endswith_period(argnames="text")
        def func(text: str) -> str:
            return text

        with caplog.at_level(logging.WARNING):
            result = func("Check nat.")
            assert result == "Check nat."
            assert "doesn't end with '.'" not in caplog.text

    def test_ensure_text_endswith_period_helper(
        self, caplog: pytest.LogCaptureFixture
    ) -> None:
        """Test the ensure_endswith_period decorator with text argument."""

        @RocqCursor.ensure_endswith_period(argnames="text")
        def func(text: str) -> str:
            return text

        with caplog.at_level(logging.WARNING):
            result = func("Check nat")
            assert result == "Check nat."
            assert "doesn't end with '.'" in caplog.text

    def test_decorator_without_parens(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test decorator usage with argnames parameter."""

        @RocqCursor.ensure_endswith_period(argnames="text")
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
            match=re.escape("at least one of argnames or return_ must be specified"),
        ):
            RocqCursor.ensure_endswith_period()(func)

    def test_complex_signature(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test a complex function signature with all parameter kinds."""

        @RocqCursor.ensure_endswith_period(
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

    def test_default_arguments_missing_period(
        self, caplog: pytest.LogCaptureFixture
    ) -> None:
        """Test that default arguments work correctly at runtime."""

        @RocqCursor.ensure_endswith_period(argnames="text")
        def func(text: str = "Check nat") -> str:
            return text

        with caplog.at_level(logging.WARNING):
            # When called without arguments, default value is used and checked
            result = func()
            assert result == "Check nat."
            assert "doesn't end with '.'" in caplog.text

    def test_multiple_parameters_some_checked(
        self, caplog: pytest.LogCaptureFixture
    ) -> None:
        """Test that only specified parameters are checked."""

        @RocqCursor.ensure_endswith_period(argnames="text1")
        def func(text1: str, text2: str, text3: str) -> tuple[str, str, str]:
            return (text1, text2, text3)

        with caplog.at_level(logging.WARNING):
            result = func("Check nat", "Check bool", "Check unit")
            assert result == ("Check nat.", "Check bool", "Check unit")
            # Only text1 should be checked
            assert caplog.text.count("doesn't end with '.'") == 1
            assert "argument 'text1'" in caplog.text

    def test_function_metadata_preserved(self) -> None:
        """Test that functools.wraps preserves function metadata."""

        @RocqCursor.ensure_endswith_period(argnames="text")
        def func(text: str) -> str:
            """A test function."""
            return text

        assert func.__name__ == "func"
        assert func.__doc__ == "A test function."

    def test_method_decorator(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test decorator on a method (with self parameter)."""

        class TestClass:
            @RocqCursor.ensure_endswith_period(argnames="text")
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
            @RocqCursor.ensure_endswith_period(argnames="text")
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
            @RocqCursor.ensure_endswith_period(argnames="text")
            def class_method(cls, text: str) -> str:
                return text

        with caplog.at_level(logging.WARNING):
            result = TestClass.class_method("Check nat")
            assert result == "Check nat."
            assert "doesn't end with '.'" in caplog.text

    def test_return_only_without_period(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test return_=True with return value that doesn't end with period."""

        @RocqCursor.ensure_endswith_period(return_=True)
        def func() -> str:
            return "Check nat"

        with caplog.at_level(logging.WARNING):
            result = func()
            assert result == "Check nat."
            assert "doesn't end with '.'" in caplog.text
            assert "return value" in caplog.text

    def test_return_only_with_period(self, caplog: pytest.LogCaptureFixture) -> None:
        """Test return_=True with return value that already ends with period."""

        @RocqCursor.ensure_endswith_period(return_=True)
        def func() -> str:
            return "Check nat."

        with caplog.at_level(logging.WARNING):
            result = func()
            assert result == "Check nat."
            assert "doesn't end with '.'" not in caplog.text

    def test_return_only_non_string_raises(self) -> None:
        """Test return_=True with non-string return value raises RuntimeError."""

        @RocqCursor.ensure_endswith_period(return_=True)
        def func() -> str:
            return 42  # type: ignore[return-value]

        with pytest.raises(
            RuntimeError,
            match=re.escape("return value is not a string"),
        ):
            func()

    def test_mixed_args_and_return_both_need_period(
        self, caplog: pytest.LogCaptureFixture
    ) -> None:
        """Test mixed argnames and return_ where both need periods added."""

        @RocqCursor.ensure_endswith_period(argnames="text", return_=True)
        def func(text: str) -> str:  # noqa: ARG001
            # Return a different value that also needs a period
            return "Check bool"

        with caplog.at_level(logging.WARNING):
            result = func("Check nat")
            # Argument gets period, return value gets period
            assert result == "Check bool."
            # Both argument and return value should trigger warnings
            assert caplog.text.count("doesn't end with '.'") == 2
            assert "argument 'text'" in caplog.text
            assert "return value" in caplog.text

    def test_mixed_args_and_return_arg_has_period(
        self, caplog: pytest.LogCaptureFixture
    ) -> None:
        """Test mixed argnames and return_ where arg has period but return doesn't."""

        @RocqCursor.ensure_endswith_period(argnames="text", return_=True)
        def func(text: str) -> str:
            return text

        with caplog.at_level(logging.WARNING):
            result = func("Check nat.")
            # Argument already has period, but return value gets checked
            # Since we return the text as-is, it already has period, so no warning
            assert result == "Check nat."
            assert "doesn't end with '.'" not in caplog.text

    def test_mixed_args_and_return_return_has_period(
        self, caplog: pytest.LogCaptureFixture
    ) -> None:
        """Test mixed argnames and return_ where return has period but arg doesn't."""

        @RocqCursor.ensure_endswith_period(argnames="text", return_=True)
        def func(text: str) -> str:  # noqa: ARG001
            _ = text
            # ...
            return "Check nat."

        with caplog.at_level(logging.WARNING):
            result = func("Check nat")
            # Argument gets period added, return value already has period
            assert result == "Check nat."
            assert caplog.text.count("doesn't end with '.'") == 1
            assert "argument 'text'" in caplog.text
            assert "return value" not in caplog.text

    def test_mixed_multiple_args_and_return(
        self, caplog: pytest.LogCaptureFixture
    ) -> None:
        """Test mixed multiple argnames and return_ all needing periods."""

        @RocqCursor.ensure_endswith_period(argnames={"text1", "text2"}, return_=True)
        def func(text1: str, text2: str) -> str:  # noqa: ARG001, ARG002
            # Return a different value that also needs a period
            _ = text1
            _ = text2
            # ...
            return "Check unit"

        with caplog.at_level(logging.WARNING):
            result = func("Check nat", "Check bool")
            # Both args get periods, then return value gets checked and period added
            assert result == "Check unit."
            assert caplog.text.count("doesn't end with '.'") == 3
            assert "argument 'text1'" in caplog.text
            assert "argument 'text2'" in caplog.text
            assert "return value" in caplog.text
