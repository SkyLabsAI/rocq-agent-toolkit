from __future__ import annotations

import json
from typing import Any, Protocol, override, runtime_checkable

from observability import get_logger
from opentelemetry.instrumentation.grpc.filters import Callable
from pydantic import BaseModel
from pydantic.dataclasses import dataclass
from pydantic.fields import Field
from rocq_doc_manager import RocqCursor
from rocq_doc_manager.rocq_doc_manager import rdm_api

logger = get_logger("task-modifier")


@runtime_checkable
class TaskModifier(Protocol):
    """A TaskModifier allow modifying a task (or its environment) before it is
    attempted. Good examples of this might be to remove hints or perform perturbations
    to the lemma statement."""

    async def run(self, rc: RocqCursor) -> None:
        """Apply the modifier to the RocqCursor."""
        ...


_json_modifiers: list[Callable[[Any], TaskModifier]] = []


def register_json_modifier(parser: Callable[[Any], TaskModifier]) -> None:
    _json_modifiers.append(parser)


def of_string(s: str | bytes | bytearray) -> TaskModifier:
    return of_json(json.loads(s))


def of_json(json: Any) -> TaskModifier:
    """Parse a `TaskModifier` from a JSON object."""
    global _modifiers
    for p in _json_modifiers:
        try:
            return p(json)
        except ValueError:
            pass
    raise ValueError(f"Failed to parse TaskModifier from '{json}'")


class InsertCommandModel(BaseModel):
    """The internal model of `InsertCommand`.

    Since `TaskModifier` is a `Protocol`, `InsertCommand` can not be a `BaseModel`.
    """

    commands: list[str] = Field(
        description="The commands to add before the task is run."
    )
    ghost: bool = Field(
        default=True,
        description="Whether the commands should be inserted as ghost commands",
        exclude_if=lambda x: x,
    )
    attempt: bool = Field(
        default=False,
        description="If true, a command that fails will be skipped (and logged), otherwise the entire modification will fail.",
        exclude_if=lambda x: not x,
    )


@dataclass
class InsertCommand(TaskModifier):
    """Insert the given commands before the task runs."""

    model: InsertCommandModel

    @staticmethod
    def make(
        commands: list[str], *, ghost: bool = True, attempt: bool = False
    ) -> InsertCommand:
        return InsertCommand(
            model=InsertCommandModel(commands=commands, ghost=ghost, attempt=attempt)
        )

    # TODO: add support for dependencies by implementing UsingRocqDeps

    @staticmethod
    def model_validate(v: Any) -> InsertCommand:
        return InsertCommand(model=InsertCommandModel.model_validate(v))

    @override
    async def run(self, rc: RocqCursor) -> None:
        for cmd in self.model.commands:
            result = await rc.insert_command(cmd, ghost=self.model.ghost)
            if isinstance(result, rdm_api.Err):
                if self.model.attempt:
                    logger.info(f"Failed to insert command: '{cmd}'")
                else:
                    raise Exception(f"Failed ot insert command: '{cmd}'")


register_json_modifier(InsertCommand.model_validate)
