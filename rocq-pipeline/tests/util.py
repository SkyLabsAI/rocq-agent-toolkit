import json


def make_task(file_path: str, locator: str) -> str:
    return json.dumps({"file": file_path, "locator": locator})
