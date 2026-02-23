import json
from typing import Any


def make_task(
    file_path: str,
    name: str | None,
    locator: str,
    tags: list[str] | None = None,
) -> dict[str, Any]:
    if tags is None:
        tags = []
    return {"file": file_path, "name": name, "locator": locator, "tags": tags}


def make_task_str(
    file_path: str,
    name: str | None,
    locator: str,
    tags: list[str] | None = None,
) -> str:
    return json.dumps(make_task(file_path, name, locator, tags=tags))


def make_repeated_tasks(
    file_path: str,
    name: str | None,
    locator: str,
    tags: list[str] | None = None,
    num_tasks: int = 1,
) -> list[dict[str, Any]]:
    return [make_task(file_path, name, locator, tags=tags)] * num_tasks


def make_repeated_tasks_str(
    file_path: str,
    name: str | None,
    locator: str,
    tags: list[str] | None = None,
    num_tasks: int = 1,
) -> str:
    return json.dumps(
        make_repeated_tasks(file_path, name, locator, tags=tags, num_tasks=num_tasks)
    )
