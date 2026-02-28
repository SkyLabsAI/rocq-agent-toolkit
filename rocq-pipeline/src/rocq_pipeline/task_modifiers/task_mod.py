from __future__ import annotations

import json
from abc import ABC, abstractmethod
from typing import Any

from observability import get_logger
from opentelemetry.instrumentation.grpc.filters import Callable
from pydantic import BaseModel
from pydantic.fields import Field
from rocq_doc_manager import RocqCursor
from rocq_doc_manager.rocq_doc_manager import rdm_api

logger = get_logger("task-modifier")


class TaskModifier(ABC):
    """A TaskModifier allow modifying a task (or its environment) before it is
    attempted. Good examples of this might be to remove hints or perform perturbations
    to the lemma statement."""

    @abstractmethod
    async def run(self, rc: RocqCursor) -> None:
        """Apply the modifier to the RocqCursor."""
        ...


_json_modifiers: list[Callable[[Any], TaskModifier]] = []


def register_json_modifier(parser: Callable[[Any], TaskModifier]) -> None:
    """It is important that each `Callable` accepts unique JSON, we do not want to
    re-interpret the meaning of a modifier."""
    _json_modifiers.append(parser)


def of_string(s: str | bytes | bytearray) -> TaskModifier:
    return of_json(json.loads(s))


def of_json(json: Any) -> TaskModifier:
    """Parse a `TaskModifier` from a JSON object."""
    global _modifiers
    for parser in _json_modifiers:
        try:
            return parser(json)
        except ValueError:
            pass
    raise ValueError(f"Failed to parse TaskModifier from '{json}'")


class InsertCommand(BaseModel, TaskModifier):
    """Insert the given commands before the task runs."""

    class Model(BaseModel):
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

    insert_command: Model = Field()

    @staticmethod
    def make(
        commands: list[str], *, ghost: bool = True, attempt: bool = False
    ) -> InsertCommand:  # valid-type
        return InsertCommand(
            insert_command=InsertCommand.Model(
                commands=commands, ghost=ghost, attempt=attempt
            )
        )

    # TODO: add support for dependencies by implementing UsingRocqDeps

    # @override # TaskModifier
    async def run(self, rc: RocqCursor) -> None:
        for cmd in self.insert_command.commands:
            result = await rc.insert_command(cmd, ghost=self.insert_command.ghost)
            if isinstance(result, rdm_api.Err):
                if self.insert_command.attempt:
                    logger.info(f"Failed to insert command: '{cmd}'")
                else:
                    raise Exception(f"Failed ot insert command: '{cmd}'")


register_json_modifier(InsertCommand.model_validate)
