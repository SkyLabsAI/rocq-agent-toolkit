import json
from typing import Any


def make_task(
    file_path: str,
    locator: str,
    tags: list[str] | None = None,
) -> dict[str, Any]:
    if tags is None:
        tags = []
    return {"file": file_path, "locator": locator, "tags": tags}


def make_task_str(
    file_path: str,
    locator: str,
    tags: list[str] | None = None,
) -> str:
    return json.dumps(make_task(file_path, locator, tags=tags))


def make_repeated_tasks(
    file_path: str,
    locator: str,
    tags: list[str] | None = None,
    num_tasks: int = 1,
) -> list[dict[str, Any]]:
    return [make_task(file_path, locator, tags=tags)] * num_tasks


def make_repeated_tasks_str(
    file_path: str,
    locator: str,
    tags: list[str] | None = None,
    num_tasks: int = 1,
) -> str:
    return json.dumps(
        make_repeated_tasks(file_path, locator, tags=tags, num_tasks=num_tasks)
    )
