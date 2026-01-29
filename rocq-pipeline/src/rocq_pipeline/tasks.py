from __future__ import annotations

import copy
import json
import os
import sys
from pathlib import Path
from typing import Any, Literal

import yaml
from pydantic import (
    BaseModel,
    ConfigDict,
    field_serializer,
    field_validator,
)
from pydantic.fields import Field

from rocq_pipeline.locator import Locator, LocatorParser


class Project(BaseModel):
    name: str = Field(description="Human readable name of the project.")
    git_url: str = Field(
        description="The URL to the repository that hosts the project."
    )
    git_commit: str = Field(
        description="The git commit hash for this project. This is important so that projects are stable."
    )
    path: Path = Field(
        description="The **local** path to the project root. This is **not** used to identify a project, it is just used for finding the tasks."
    )

    @field_serializer("path")
    def serialize_path(self, path: Path):
        return str(path)

    def get_id(self) -> str:
        return f"{self.git_url}#{self.git_commit}"


class Task(BaseModel):
    model_config = ConfigDict(arbitrary_types_allowed=True)

    name: str | None = Field(
        None,
        description="Human-readable name of the task. This can be used to distinguish multiple tasks on the same locator, e.g. 'with-prompt' and 'without-prompt'",
        exclude_if=lambda x: x is None,
    )
    file: Path = Field(
        description="The path from the project root to the file that hosts the task."
    )
    locator: Locator = Field(description="The location within the file.")
    tags: set[str] = Field(
        description="The tags of the task. These are often used to convey information such as how complex a task is. These are easily searchable within the dashboard."
    )
    prompt: str | None = Field(
        default=None,
        description="Additional information about the task **provided to the agent**.",
        exclude_if=lambda x: x is None,
    )
    meta: dict[str, Any] | None = Field(
        default=None,
        description="Meta data about the task as a JSON dictionary, e.g. 'ground truth' proof script.",
        exclude_if=lambda x: not bool(x),
    )  # The [Any] is json-able things

    def get_id(self) -> str:
        if self.name is not None:
            return self.name
        return f"{self.file}#{self.locator}"

    def get_tags(self) -> set[str]:
        return self.tags

    @field_validator("file")
    @classmethod
    def validate_path(cls, p: Path) -> Path:
        if p.is_absolute():
            raise ValueError(f"Path {p} is not relative")
        if p.suffix != ".v":
            raise ValueError(f'Path {p} does not have the ".v" extension')
        return p

    @field_validator("locator", mode="before")
    @classmethod
    def parse_locator_string(cls, value: str | Locator) -> Locator:
        if isinstance(value, Locator):
            return value
        return LocatorParser.parse(value)

    @field_validator("tags")
    @classmethod
    def parse_tags_set(cls, value: set[str] | list[str]) -> set[str]:
        if isinstance(value, set):
            return value
        return set(value)

    @field_serializer("file")
    def serialize_path(self, path: Path):
        return str(path)

    @field_serializer("tags")
    def serialize_tags(self, tags: set[str]):
        return sorted(tags)

    @field_serializer("locator")
    def serialize_locator(self, locator: Locator):
        return str(locator)


class TaskFile(BaseModel):
    project: Project
    tasks: list[Task]

    @classmethod
    def from_file(cls, file: Literal["-"] | Path) -> TaskFile:
        data: dict[str, Any] = {}

        if file == "-":
            data = json.load(sys.stdin)
        else:
            with open(file, encoding="utf-8") as f:
                if file.suffix in [".yaml", ".yml"]:
                    data = yaml.safe_load(f)
                elif file.suffix in [".json"]:
                    data = json.load(f)
                else:
                    raise ValueError(
                        "Invalid tasks file extension. Expected `.json`, "
                        "`.yaml`, or `.yml`"
                    )

        task_file = TaskFile.model_validate(data)
        file_dir = Path(".") if file == "-" else file.parent
        path = file_dir / task_file.project.path
        task_file.project.path = Path(os.path.normpath(path))

        return task_file

    def to_file(self, file: Literal["-"] | Path) -> None:
        project = copy.deepcopy(self.project)
        tasks = sorted(self.tasks, key=lambda t: (t.file, t.name, str(t.locator)))
        task_file = TaskFile(project=project, tasks=tasks)

        file_dir = Path(".") if file == "-" else file.parent
        task_file.project.path = task_file.project.path.resolve().relative_to(
            file_dir.resolve(), walk_up=True
        )

        data = task_file.model_dump(exclude_none=True)

        if file == "-":
            json.dump(data, sys.stdout, indent=2)
            sys.stdout.write("\n")
        else:
            with open(file, "w") as f:
                if file.suffix in [".yaml", ".yml"]:
                    yaml.safe_dump(data, f, sort_keys=False)
                elif file.suffix in [".json"]:
                    json.dump(data, f, indent=2)
                else:
                    raise ValueError(
                        "Invalid tasks file extension. Expected `.json`, "
                        "`.yaml`, or `.yml`"
                    )

    def filter_tags(self, tag: str) -> TaskFile:
        tasks = [t for t in self.tasks if tag in t.get_tags()]
        return TaskFile(project=self.project, tasks=tasks)

    @classmethod
    def supported_extensions(cls) -> list[str]:
        return [".json", ".yaml", ".yml"]

    @classmethod
    def valid_extension(cls, file: Path) -> bool:
        return file.suffix in TaskFile.supported_extensions()
