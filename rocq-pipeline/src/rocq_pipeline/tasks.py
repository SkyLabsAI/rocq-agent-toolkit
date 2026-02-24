from __future__ import annotations

import copy
import json
import os
import sys
from argparse import ArgumentParser, Namespace
from collections import defaultdict
from collections.abc import Iterator
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
from rocq_doc_manager.locator import Locator, LocatorParser

from rocq_pipeline.schema.task_output import FullProofTask, TaskKind
from rocq_pipeline.task_modifiers import task_mod
from rocq_pipeline.task_modifiers.task_mod import TaskModifier


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
        default_factory=set,
        description="The tags of the task. These are often used to convey information such as how complex a task is. These are easily searchable within the dashboard.",
        exclude_if=lambda x: not x,
    )
    prompt: str | None = Field(
        default=None,
        description="Additional information about the task **provided to the agent**.",
        exclude_if=lambda x: x is None,
    )
    modifiers: list[TaskModifier] = Field(
        default_factory=list,
        description="Modifiers that should be run before the task is attempted.",
        exclude_if=lambda x: not x,
    )
    meta: dict[str, Any] | None = Field(
        default=None,
        description="Meta data about the task as a JSON dictionary, e.g. 'ground truth' proof script.",
        exclude_if=lambda x: not bool(x),
    )  # The [Any] is json-able things

    def get_kind(self) -> TaskKind:
        return TaskKind(FullProofTask())

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

    @field_validator("modifiers", mode="before")
    @classmethod
    def parse_modifiers(cls, v: Any) -> list[TaskModifier]:
        if not isinstance(v, list):
            return v

        return [task_mod.of_json(elem) for elem in v]

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
    """A collection of tasks attached to the same Project."""

    project: Project = Field(description="The Project that the tasks belong to.")
    tasks: list[Task] = Field(description="The Tasks in the project.")

    def build_deps(self) -> list[Path]:
        """Enumerate the .vo dependencies for tasks in the project relative to cwd."""
        root_path = self.project.path.resolve().relative_to(
            Path(".").resolve(), walk_up=True
        )
        targets: list[Path] = []

        for task in self.tasks:
            v_abspath = (root_path / task.file).resolve(strict=True)
            v_relpath = v_abspath.relative_to(Path(".").resolve(), walk_up=True)
            targets.append(v_relpath.with_suffix(".vo"))

        return targets

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
    project_bundles: list[TaskBundle] = Field(
        description="Bundles of projects and their associatd tasks"
    )

    def build_deps(self) -> list[Path]:
        """Enumerate the .vo dependencies for all project_bundles relative to cwd."""
        targets: list[Path] = []
        for project_bundle in self.project_bundles:
            targets.extend(project_bundle.build_deps())
        return targets

    @model_validator(mode="after")
    def merge_bundles(self) -> TaskFile:
        """Merge bundles with the same project and deduplicate tasks."""
        self.project_bundles = TaskBundle.merge(self.project_bundles)
        return self

    @model_serializer
    def serialize_model(self) -> dict[str, Any]:
        """Serialize TaskFile as a list of TaskBundle data (on-disk format)."""
        sorted_bundles = sorted(self.project_bundles, key=lambda b: b.project.get_id())
        # Tasks are already sorted by TaskBundle serializer
        return {"project_bundles": [bundle.model_dump() for bundle in sorted_bundles]}

    @classmethod
    def from_tasks(cls, tasks: Iterator[tuple[Project, Task]]):
        projs: defaultdict[Project, list[Task]] = defaultdict(list)
        for proj, task in tasks:
            proj_tasks = projs.get(proj)
            assert proj_tasks is not None
            proj_tasks.append(task)
        return TaskFile(
            project_bundles=[
                TaskBundle(project=proj, tasks=tasks) for proj, tasks in projs.items()
            ]
        )

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
        if isinstance(raw_data, dict):
            if "project_bundles" in raw_data:
                # Legacy new format: dict with "bundles" key
                bundles_data = raw_data["project_bundles"]
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
            raise ValueError(f"Expected dict, got {type(raw_data).__name__}")

        task_file = TaskFile.model_validate({"project_bundles": bundles_data})
        file_dir = Path(".") if file == "-" else file.parent

        # Resolve paths for all projects
        for bundle in task_file.project_bundles:
            path = file_dir / bundle.project.path
            bundle.project.path = Path(os.path.normpath(path))

        return task_file

    def to_file(self, file: Literal["-"] | Path) -> None:
        # Create a copy to avoid modifying the original
        bundles = copy.deepcopy(self.project_bundles)

        file_dir = Path(".") if file == "-" else file.parent

        # Relativize paths for all projects
        for bundle in bundles:
            bundle.project.path = bundle.project.path.resolve().relative_to(
                file_dir.resolve(), walk_up=True
            )

        task_file = TaskFile(project_bundles=bundles)
        # Serialize as list (on-disk format)
        data = task_file.model_dump(mode="json", exclude_none=True)

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
        return TaskFile(project_bundles=task_bundles)

    @classmethod
    def cli_build_deps_mk_parser(cls, parent: Any | None = None) -> ArgumentParser:
        """Used in ./cli.py to expose a 'build-deps' subcommand of 'rat'."""
        description = "Enumerate .vo build targets relative to cwd for a single task_file."
        help = "Supply a path to a single task file and enumerate its .vo dependencies relative to cwd."
        if parent:
            parser = parent.add_parser("build-deps", description=description, help=help)
        else:
            parser = ArgumentParser(description=description)
        parser.add_argument(
            "task_file", type=Path, help="The path to a single task file"
        )
        return parser

    @classmethod
    def cli_build_deps_run_ns(
        cls, arguments: Namespace, extra_args: list[str] | None = None
    ) -> None:
        """Used in ./cli.py to expose a 'build-deps' subcommand of 'rat'."""
        assert extra_args is None or len(extra_args) == 0
        taskfile = cls.from_file(arguments.task_file)
        print(" ".join([str(vo_path) for vo_path in taskfile.build_deps()]))

    def iter_tasks(self) -> Iterator[tuple[Project, Task]]:
        """Get all tasks from all bundles."""
        for bundle in self.project_bundles:
            for task in bundle.tasks:
                yield (bundle.project, task)

    def iter_projects_with_tasks(self) -> Iterator[tuple[Project, list[Task]]]:
        """Get all projects from bundles."""
        for bundle in self.project_bundles:
            yield bundle.project, bundle.tasks
