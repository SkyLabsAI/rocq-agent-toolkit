import yaml
import json
import jmespath
import os.path

def load_tasks(filename: str) -> tuple[str, list[dict]]:
    """
    Load tasks from a task file and returns the working directory
    path and the map of tasks.

    Supported file formats: Yaml (.yaml or .yml), Json (.json)
    """
    wdir = os.path.dirname(filename)
    with open(filename, 'r') as f:
        if filename.endswith('.yaml') or filename.endswith('.yml'):
            return (wdir, yaml.safe_load(f))
        elif filename.endswith('.json'):
            return (wdir, json.load(f))

    raise ValueError("Invalid tasks file extension. Expected `.json`, `.yaml`, or `.yml`")

def filter_tags(tasks : list[dict], tag : str) -> list[dict]:
    """Get all the tasks that contain the given tag"""
    escaped = tag.replace("'", r"\'")
    return jmespath.search(f"[? contains(tags, '{escaped}')]", tasks)
