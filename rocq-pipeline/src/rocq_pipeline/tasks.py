import json
import sys
from pathlib import Path
from typing import Any, cast

import jmespath
import yaml

type Task = dict[str, Any]


def get_task_id(task: Task) -> str:
    validate_task_schema(task)
    return f"{task['file']}#{task['locator']}"


def get_task_tags(task: Task) -> set[str]:
    validate_task_schema(task)
    return set(task.get("tags", []))


def validate_task_schema(task: Task) -> None:
    if not isinstance(task, dict):
        raise ValueError(
            f"Task should be a dict, but had type {type(task)}: {task}"
        )

    expected_keys = {"file", "locator"}
    if not (expected_keys <= task.keys()):
        raise ValueError(" ".join([
            f"Task should contain at least ({', '.join(expected_keys)}),",
            f"but had ({', '.join(task.keys())}): {task}"
        ]))
    for k in expected_keys:
        v = task[k]
        assert isinstance(v, str), \
            f"{k} should be a str, but got {type(v)}: {v}"

    if "tags" in task.keys():
        tags = task["tags"]
        assert isinstance(tags, list), \
            f"tags should be a list, but got {type(tags)}: {tags}"
        for tag in tags:
            assert isinstance(tag, str), \
                f"tag should be a str, but got {type(tag)}: {tag}"

    if Path(task["file"]).suffix != ".v":
        raise ValueError("Task file should be a Rocq file (.v): {task}")


def validate_tasklist_schema(tasks: list[Task]) -> None:
    assert isinstance(tasks, list)
    for task in tasks:
        validate_task_schema(task)


def mk_validated_tasklist(
        data: dict[str, Any] | list[dict[str, Any]]
) -> list[Task]:
    if isinstance(data, dict):
        data = [data]
    validate_tasklist_schema(data)
    return data

def load_tasks(filename: str | Path) -> tuple[Path, list[Task]]:
    if filename == "-":
        return (Path("."), json.load(sys.stdin))

    filename = Path(filename)
    wdir = filename.parent
    with open(filename, encoding="utf-8") as f:
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

def save_tasks(filename: str | Path, tasks: list[Task]) -> None:
    if filename == "-":
        json.dump(tasks, sys.stdout)
    filename = Path(filename)
    with open(filename, 'w') as f:
        if filename.suffix in [".yaml",".yml"]:
            yaml.safe_dump(tasks, f)
        elif filename.suffix in [".json"]:
            json.dump(tasks, f)
        else:
            raise ValueError("Invalid file extension. Expected `.json`, `.yaml`, or `.yml`")

def filter_tags(tasks: list[Task], tag: str) -> list[Task]:
    escaped = tag.replace("'", r"\'")
    return cast(
        list[Task],
        jmespath.search(f"[? contains(tags, '{escaped}')]", tasks)
    )
