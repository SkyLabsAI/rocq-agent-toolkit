"""Task management utilities for loading and filtering proof tasks.

This module provides functionality to load tasks from various file formats
and filter them based on tags or other criteria.
"""

import yaml
import json
import jmespath
from pathlib import Path
from typing import List, Dict, Any, Tuple


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
            return (wdir, yaml.safe_load(f))
        elif filename.suffix in [".json"]:
            return (wdir, json.load(f))

    raise ValueError(
        "Invalid tasks file extension. Expected `.json`, `.yaml`, or `.yml`"
    )


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
    return jmespath.search(f"[? contains(tags, '{escaped}')]", tasks)
