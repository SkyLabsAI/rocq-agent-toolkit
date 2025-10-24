import json
from pathlib import Path
from typing import Any, Dict, List, Tuple, cast

import jmespath
import yaml


def load_tasks(filename: str | Path) -> tuple[Path, list[dict[str, Any]]]:
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


def filter_tags(tasks: list[dict[str, Any]], tag: str) -> list[dict[str, Any]]:
    escaped = tag.replace("'", r"\'")
    return cast(
        list[Dict[str, Any]],
        jmespath.search(f"[? contains(tags, '{escaped}')]", tasks)
    )
