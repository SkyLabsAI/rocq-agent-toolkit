"""Utility functions for testing.

This module contains common utility functions used across test modules
in the rocq_pipeline test suite.
"""

import json


def make_task(file_path: str, locator: str) -> str:
    """Create a JSON task configuration.

    Args:
        file_path: Path to the Coq theory file.
        locator: The locator string for the specific lemma or theorem.

    Returns:
        A JSON string containing the task configuration.
    """
    return json.dumps({"file": file_path, "locator": locator})
