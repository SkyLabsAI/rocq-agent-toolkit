import logging

import pytest
from rocq_doc_manager import RocqCursor
from rocq_doc_manager.rocq_doc_manager import RocqDocManager

from .util import RDM_Tests


class Test_RocqCursor_ensure_text_endswith_period(RDM_Tests):
    """Test the ensure_text_endswith_period decorator usage in RocqCursor methods."""

    def test_insert_command_with_period_no_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test insert_command with text ending in period - no warning."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            result = rc.insert_command("Check nat.")
            assert not isinstance(result, RocqCursor.Err)
            assert "doesn't end with '.'" not in caplog.text

    def test_insert_command_without_period_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test insert_command with text not ending in period - warning logged."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            result = rc.insert_command("Check nat")
            assert not isinstance(result, RocqCursor.Err)
            assert "doesn't end with '.'" in caplog.text
            assert "insert_command" in caplog.text
            assert "argument 'text'" in caplog.text

    def test_query_with_period_no_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test query with text ending in period - no warning."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            result = rc.query("Check nat.")
            assert not isinstance(result, RocqCursor.Err)
            assert "doesn't end with '.'" not in caplog.text

    def test_query_without_period_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test query with text not ending in period - warning logged."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            result = rc.query("Check nat")
            assert not isinstance(result, RocqCursor.Err)
            assert "doesn't end with '.'" in caplog.text
            assert "query" in caplog.text

    def test_query_json_with_period_no_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test query_json with text ending in period - no warning."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            # Note: query_json may return an error if the query doesn't return JSON,
            # but we're testing the decorator, not the query result
            rc.query_json("Check nat.", 0)
            assert "doesn't end with '.'" not in caplog.text

    def test_query_json_without_period_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test query_json with text not ending in period - warning logged."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            # Note: query_json may return an error if the query doesn't return JSON,
            # but we're testing the decorator, not the query result
            rc.query_json("Check nat", 0)
            assert "doesn't end with '.'" in caplog.text
            assert "query_json" in caplog.text

    def test_query_json_all_with_period_no_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test query_json_all with text ending in period - no warning."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            # Note: query_json_all may return an error if the query doesn't return JSON,
            # but we're testing the decorator, not the query result
            rc.query_json_all("Check nat.")
            assert "doesn't end with '.'" not in caplog.text

    def test_query_json_all_without_period_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test query_json_all with text not ending in period - warning logged."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            # Note: query_json_all may return an error if the query doesn't return JSON,
            # but we're testing the decorator, not the query result
            rc.query_json_all("Check nat")
            assert "doesn't end with '.'" in caplog.text
            assert "query_json_all" in caplog.text

    def test_query_text_with_period_no_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test query_text with text ending in period - no warning."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            result = rc.query_text("Check nat.", 0)
            assert not isinstance(result, RocqCursor.Err)
            assert "doesn't end with '.'" not in caplog.text

    def test_query_text_without_period_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test query_text with text not ending in period - warning logged."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            result = rc.query_text("Check nat", 0)
            assert not isinstance(result, RocqCursor.Err)
            assert "doesn't end with '.'" in caplog.text
            assert "query_text" in caplog.text

    def test_query_text_all_with_period_no_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test query_text_all with text ending in period - no warning."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            result = rc.query_text_all("Check nat.")
            assert not isinstance(result, RocqCursor.Err)
            assert "doesn't end with '.'" not in caplog.text

    def test_query_text_all_without_period_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test query_text_all with text not ending in period - warning logged."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            result = rc.query_text_all("Check nat")
            assert not isinstance(result, RocqCursor.Err)
            assert "doesn't end with '.'" in caplog.text
            assert "query_text_all" in caplog.text

    def test_run_command_with_period_no_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test run_command with text ending in period - no warning."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            result = rc.run_command("Check nat.")
            assert not isinstance(result, RocqCursor.Err)
            assert "doesn't end with '.'" not in caplog.text

    def test_run_command_without_period_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test run_command with text not ending in period - warning logged."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            result = rc.run_command("Check nat")
            assert not isinstance(result, RocqCursor.Err)
            assert "doesn't end with '.'" in caplog.text
            assert "run_command" in caplog.text

    def test_insert_command_keyword_arg_with_period_no_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test insert_command with keyword argument ending in period - no warning."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            result = rc.insert_command(text="Check nat.")
            assert not isinstance(result, RocqCursor.Err)
            assert "doesn't end with '.'" not in caplog.text

    def test_insert_command_keyword_arg_without_period_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test insert_command with keyword argument not ending in period - warning logged."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            result = rc.insert_command(text="Check nat")
            assert not isinstance(result, RocqCursor.Err)
            assert "doesn't end with '.'" in caplog.text
            assert "insert_command" in caplog.text

    def test_query_json_all_with_indices_without_period_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test query_json_all with indices parameter and text not ending in period - warning logged."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            # Note: query_json_all may return an error if the query doesn't return JSON,
            # but we're testing the decorator, not the query result
            rc.query_json_all("Check nat", indices=[0])
            assert "doesn't end with '.'" in caplog.text
            assert "query_json_all" in caplog.text

    def test_query_text_all_with_indices_without_period_warning(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test query_text_all with indices parameter and text not ending in period - warning logged."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            result = rc.query_text_all("Check nat", indices=[0])
            assert not isinstance(result, RocqCursor.Err)
            assert "doesn't end with '.'" in caplog.text
            assert "query_text_all" in caplog.text

    def test_multiple_calls_accumulate_warnings(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test that multiple calls without periods accumulate warnings."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            rc.insert_command("Check nat")
            rc.query("Check bool")
            rc.run_command("Check unit")
            assert caplog.text.count("doesn't end with '.'") == 3
            assert "insert_command" in caplog.text
            assert "query" in caplog.text
            assert "run_command" in caplog.text

    def test_period_added_automatically(
        self, caplog: pytest.LogCaptureFixture, transient_rdm: RocqDocManager
    ) -> None:
        """Test that period is automatically added when missing."""
        rc = transient_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            # The decorator should add the period automatically
            result = rc.insert_command("Check nat")
            assert not isinstance(result, RocqCursor.Err)
            # Verify the command was actually executed with the period added
            # by checking the document prefix (where inserted commands go)
            prefix = rc.doc_prefix()
            # The command should have been inserted, so prefix should contain it
            assert len(prefix) > 0
            # Find the command we just inserted
            command_items = [item for item in prefix if item.kind == "command"]
            if command_items:
                # The last command should end with a period (added by decorator)
                assert command_items[-1].text.endswith(".")
