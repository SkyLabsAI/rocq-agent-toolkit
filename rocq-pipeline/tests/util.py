import json


def make_repeated_tasks(file_path: str, locator: str, num_tasks: int = 1) -> str:
    tasks = [{"file": file_path, "locator": locator}] * num_tasks
    return json.dumps(tasks)


def make_task(file_path: str, locator: str) -> str:
    return json.dumps({"file": file_path, "locator": locator})
