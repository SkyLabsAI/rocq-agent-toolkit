import json
from pathlib import Path
from typing import Any, Dict, List, Tuple, cast

import jmespath
import yaml


def validate_task_schema(task: dict[str, Any]) -> None:
    assert isinstance(task, dict)
    assert {"file", "locator"} <= task.keys()


def validate_tasklist_schema(tasks: list[dict[str, Any]]) -> None:
    assert isinstance(tasks, list)
    for task in tasks:
        validate_task_schema(task)


def mk_validated_tasklist(
        data: dict[str, Any] | list[dict[str, Any]]
) -> list[dict[str, Any]]:
    if isinstance(data, dict):
        data = [data]
    validate_tasklist_schema(data)
    return data


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

        return (wdir, mk_validated_tasklist(data))


def filter_tags(tasks: list[dict[str, Any]], tag: str) -> list[dict[str, Any]]:
    escaped = tag.replace("'", r"\'")
    return cast(
        list[Dict[str, Any]],
        jmespath.search(f"[? contains(tags, '{escaped}')]", tasks)
    )
