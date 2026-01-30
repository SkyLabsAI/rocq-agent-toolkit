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
    model_serializer,
    model_validator,
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


class TaskBundle(BaseModel):
    project: Project
    tasks: list[Task]

    @field_serializer("tasks")
    def serialize_tasks(self, tasks: list[Task]):
        return sorted(tasks, key=lambda t: (t.file, t.name, str(t.locator)))

    @classmethod
    def merge(cls, bundles: list[TaskBundle]) -> list[TaskBundle]:
        """Merge bundles with the same project and deduplicate tasks."""
        # Use hashable tuple key for O(1) lookups (Project isn't hashable due to Path)
        # Key: (name, git_url, git_commit, path_str)
        # Value: (Project object, list of tasks)
        project_data: dict[tuple[str, str, str, str], tuple[Project, list[Task]]] = {}

        for bundle in bundles:
            # Create hashable key from project fields
            project_key = (
                bundle.project.name,
                bundle.project.git_url,
                bundle.project.git_commit,
                str(bundle.project.path),
            )

            if project_key not in project_data:
                # New project
                project_data[project_key] = (bundle.project, [])

            project, tasks = project_data[project_key]

            # Merge tasks, deduplicating by Task.get_id()
            seen_task_ids = {task.get_id() for task in tasks}

            for task in bundle.tasks:
                task_id = task.get_id()
                if task_id not in seen_task_ids:
                    tasks.append(task)
                    seen_task_ids.add(task_id)

        # Create merged bundles
        return [
            cls(project=project, tasks=tasks)
            for project, tasks in project_data.values()
        ]


class TaskFile(BaseModel):
    bundles: list[TaskBundle]

    @model_validator(mode="after")
    def merge_bundles(self) -> TaskFile:
        """Merge bundles with the same project and deduplicate tasks."""
        merged_bundles = TaskBundle.merge(self.bundles)
        # Use model_construct to avoid re-validation (which would cause recursion)
        return self.model_construct(bundles=merged_bundles)

    @model_serializer
    def serialize_model(self) -> list[dict[str, Any]]:
        """Serialize TaskFile as a list of TaskBundle data (on-disk format)."""
        sorted_bundles = sorted(self.bundles, key=lambda b: b.project.get_id())
        # Tasks are already sorted by TaskBundle serializer
        return [bundle.model_dump() for bundle in sorted_bundles]

    @classmethod
    def from_file(cls, file: Literal["-"] | Path) -> TaskFile:
        # Load raw data
        raw_data: Any
        if file == "-":
            raw_data = json.load(sys.stdin)
        else:
            with open(file, encoding="utf-8") as f:
                if file.suffix in [".yaml", ".yml"]:
                    raw_data = yaml.safe_load(f)
                elif file.suffix in [".json"]:
                    raw_data = json.load(f)
                else:
                    raise ValueError(
                        "Invalid tasks file extension. Expected `.json`, "
                        "`.yaml`, or `.yml`"
                    )

        # Determine format and convert to internal format
        bundles_data: list[dict[str, Any]]
        if isinstance(raw_data, list):
            # New format: list of TaskBundle data
            bundles_data = raw_data
        elif isinstance(raw_data, dict):
            if "bundles" in raw_data:
                # Legacy new format: dict with "bundles" key
                bundles_data = raw_data["bundles"]
            elif "project" in raw_data and "tasks" in raw_data:
                # Old format: single project with tasks
                bundle = TaskBundle(
                    project=raw_data["project"], tasks=raw_data["tasks"]
                )
                bundles_data = [bundle.model_dump()]
            else:
                raise ValueError(
                    "Invalid task file format. Expected either a list of bundles (new format), "
                    "a dict with 'bundles' key, or a dict with 'project' and 'tasks' (old format)."
                )
        else:
            raise ValueError(f"Expected list or dict, got {type(raw_data).__name__}")

        task_file = TaskFile.model_validate({"bundles": bundles_data})
        file_dir = Path(".") if file == "-" else file.parent

        # Resolve paths for all projects
        for bundle in task_file.bundles:
            path = file_dir / bundle.project.path
            bundle.project.path = Path(os.path.normpath(path))

        return task_file

    def to_file(self, file: Literal["-"] | Path) -> None:
        # Create a copy to avoid modifying the original
        bundles = copy.deepcopy(self.bundles)

        file_dir = Path(".") if file == "-" else file.parent

        # Relativize paths for all projects
        for bundle in bundles:
            bundle.project.path = bundle.project.path.resolve().relative_to(
                file_dir.resolve(), walk_up=True
            )

        task_file = TaskFile(bundles=bundles)
        # Serialize as list (on-disk format)
        data = task_file.model_dump(mode="json")

        if file == "-":
            json.dump(data, sys.stdout, indent=2)
            sys.stdout.write("\n")
        else:
            with open(file, "w", encoding="utf-8") as f:
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
        """Filter tasks across all bundles by tag, removing empty bundles."""
        filtered_bundles = []
        for bundle in self.bundles:
            filtered_tasks = [t for t in bundle.tasks if tag in t.get_tags()]
            if filtered_tasks:
                filtered_bundles.append(
                    TaskBundle(project=bundle.project, tasks=filtered_tasks)
                )
        return TaskFile(bundles=filtered_bundles)

    @classmethod
    def supported_extensions(cls) -> list[str]:
        return [".json", ".yaml", ".yml"]

    @classmethod
    def valid_extension(cls, file: Path) -> bool:
        return file.suffix in TaskFile.supported_extensions()

    @classmethod
    def from_bundles(cls, bundles: list[tuple[Project, list[Task]]]) -> TaskFile:
        """Convenience method to create TaskFile from (project, tasks) pairs."""
        task_bundles = [
            TaskBundle(project=project, tasks=tasks) for project, tasks in bundles
        ]
        return TaskFile(bundles=task_bundles)

    def get_all_tasks(self) -> list[Task]:
        """Get all tasks from all bundles. Useful for backward compatibility."""
        return [task for bundle in self.bundles for task in bundle.tasks]

    def get_all_projects(self) -> list[Project]:
        """Get all unique projects from bundles."""
        return [bundle.project for bundle in self.bundles]

    @property
    def project(self) -> Project:
        """Get the project from a single-project TaskFile. Raises ValueError if multiple projects."""
        if len(self.bundles) != 1:
            raise ValueError(
                f"TaskFile has {len(self.bundles)} projects. "
                "Use .bundles or .get_all_projects() for multi-project files."
            )
        return self.bundles[0].project

    @property
    def tasks(self) -> list[Task]:
        """Get the tasks from a single-project TaskFile. Raises ValueError if multiple projects."""
        if len(self.bundles) != 1:
            raise ValueError(
                f"TaskFile has {len(self.bundles)} projects. "
                "Use .bundles or .get_all_tasks() for multi-project files."
            )
        return self.bundles[0].tasks
