from __future__ import annotations

import re
from typing import Protocol, override

from observability import get_logger
from opentelemetry.instrumentation.grpc.filters import Callable
from pydantic.dataclasses import dataclass
from pydantic.fields import Field
from rocq_doc_manager import RocqCursor
from rocq_doc_manager.rocq_doc_manager import rdm_api

logger = get_logger("task-manipulator")


class TaskModifier(Protocol):
    """A TaskModifier allow modifying a task (or its environment) before it is
    attempted. Good examples of this might be to remove hints or perform perturbations
    to the lemma statement."""

    async def run(self, rc: RocqCursor) -> None:
        """Apply the modifier to the RocqCursor."""
        ...


_modifiers: list[Callable[[str], TaskModifier]] = []


def register_modifier(parser: Callable[[str], TaskModifier]) -> None:
    _modifiers.append(parser)


def of_string(s: str) -> TaskModifier:
    global _modifiers
    for p in _modifiers:
        try:
            return p(s)
        except ValueError:
            pass
    raise ValueError(f"Failed to parse TaskModifier from '{s}'")


@dataclass
class InsertCommand(TaskModifier):
    """Insert the given commands before the task runs."""

    commands: list[str] = Field(
        description="The commands to add before the task is run."
    )
    ghost: bool = Field(
        default=True,
        description="Whether the commands should be inserted as ghost commands",
    )
    attempt: bool = Field(
        default=False,
        description="If true, a command that fails will be skipped (and logged), otherwise the entire modification will fail.",
    )

    _PTRN = re.compile(r"^insert-command(\?)?:\s*(.*)\.$")

    @staticmethod
    def parse(s: str) -> InsertCommand:
        mtch = InsertCommand._PTRN.match(s)
        if mtch:
            return InsertCommand(commands=[mtch.group(2)], attempt=bool(mtch.group(1)))
        raise ValueError(f"Failed to parse InsertCommand from '{s}'")

    @override
    async def run(self, rc: RocqCursor) -> None:
        for cmd in self.commands:
            result = await rc.insert_command(cmd)
            if isinstance(result, rdm_api.Err):
                if self.attempt:
                    logger.info(f"Failed to insert command: '{cmd}'")
                else:
                    raise Exception(f"Failed ot insert command: '{cmd}'")
