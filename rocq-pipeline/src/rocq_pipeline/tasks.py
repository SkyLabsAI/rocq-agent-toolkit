"""Task management utilities for loading and filtering proof tasks.

This module provides functionality to load tasks from various file formats
and filter them based on tags or other criteria.
"""

import json
from pathlib import Path
from typing import Any, Dict, List, Tuple, cast

import jmespath
import yaml


def load_tasks(filename: str | Path) -> Tuple[Path, List[Dict[str, Any]]]:
    """Load tasks from a task file and return the working directory and task list.

    This function supports loading tasks from YAML and JSON files. The working
    directory is set to the directory containing the task file.

    Args:
        filename: Path to the task file to load.

    Returns:
        A tuple containing:
        - The working directory path (directory of the task file)
        - A list of task dictionaries

    Raises:
        ValueError: If the file extension is not supported.
        FileNotFoundError: If the task file does not exist.
    """
    filename = Path(filename)
    wdir = filename.parent
    with open(filename, "r", encoding="utf-8") as f:
        if filename.suffix in [".yaml", ".yml"]:
            data = yaml.safe_load(f)
        elif filename.suffix in [".json"]:
            data = json.load(f)
        else:
            raise ValueError(" ".join([
                "Invalid tasks file extension.",
                "Expected `.json`, `.yaml`, or `.yml`",
            ]))

        # in case someone has a single task in a file
        if isinstance(data, dict):
            data = [data]

        if not isinstance(data, list):
            raise ValueError(" ".join([
                "Invalid task contents.",
                "Expected a (list of) tasks.",
            ]))

        return (wdir, data)


def filter_tags(tasks: List[Dict[str, Any]], tag: str) -> List[Dict[str, Any]]:
    """Filter tasks that contain the specified tag.

    This function uses JMESPath to search for tasks that contain the given tag
    in their tags list.

    Args:
        tasks: List of task dictionaries to filter.
        tag: The tag to search for in the tasks.

    Returns:
        A list of tasks that contain the specified tag.
    """
    escaped = tag.replace("'", r"\'")
    return cast(
        List[Dict[str, Any]],
        jmespath.search(f"[? contains(tags, '{escaped}')]", tasks)
    )
