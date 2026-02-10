#
# This file provides a simple script that tests tool calls
#

import asyncio
import sys
from collections.abc import Generator
from contextlib import contextmanager
from pathlib import Path
from typing import Any

from pydantic_ai.agent import Agent
from pydantic_ai.messages import ModelMessage, ModelResponse, TextPart, ToolCallPart
from pydantic_ai.models import Model
from pydantic_ai.models.function import AgentInfo, FunctionModel
from pydantic_ai.run import AgentRunResult
from rocq_doc_manager import RocqCursor, RocqDocManager
from rocq_doc_manager.locator import Locator, LocatorParser
from rocq_pipeline.tasks import json

from rocq_agent_tools_pydantic.tools import RocqProofStateDeps, rocq_cursor_toolset


@contextmanager
def build_cursor(filename: Path, loc: Locator) -> Generator[RocqCursor]:
    rdm = RocqDocManager([], str(filename.name), chdir=str(filename.parent), dune=True)
    rc = rdm.cursor()
    load_result = rc.load_file()
    if load_result is not None:
        print(load_result)
        raise AssertionError
    assert loc(rc)

    try:
        yield rc
    finally:
        rc.dispose()
        rdm.quit()


def build_model(calls: list[tuple[str, Any]]) -> Model:
    calls = calls.copy()

    def handler(messages: list[ModelMessage], info: AgentInfo) -> ModelResponse:
        nonlocal calls
        try:
            tool_name, args = calls.pop(0)
            return ModelResponse(parts=[ToolCallPart(tool_name=tool_name, args=args)])

        except IndexError:
            return ModelResponse(parts=[TextPart(content="Done")])

    return FunctionModel(handler)


async def amain(args: list[str]) -> None:
    if len(args) < 2:
        raise ValueError("Insufficient arguments")
    file = Path(args.pop(0))
    locator = LocatorParser.parse(args.pop(0))

    def parse_tool_call(s: str) -> tuple[str, Any]:
        js = json.loads(s)
        if isinstance(js, str):
            return (js, {})
        if isinstance(js, list):
            assert len(js) == 2
            return (js[0], js[1])
        raise ValueError(f"Parsing tool call from: {s}")

    messages = [parse_tool_call(arg) for arg in args]

    with build_cursor(file, locator) as rc:
        deps = RocqProofStateDeps(rc)
        agent = Agent(
            build_model(messages),
            system_prompt="Tool call testing",
            deps_type=RocqProofStateDeps,
            toolsets=[rocq_cursor_toolset],
        )
        result: AgentRunResult = await agent.run(deps=deps)

        # All the information
        # print(json.dumps(json.loads(result.all_messages_json()), indent=2))

        # It is necessary to remove some information, e.g. timestamps and nonces
        # in order to get repeatable output.
        for msg in result.all_messages():
            for part in msg.parts:
                if part.part_kind == "tool-return":
                    print(f"= {part.content}")
                elif part.part_kind == "tool-call":
                    print(f"{part.tool_name}({part.args})")


def main():
    asyncio.run(amain(sys.argv[1:]))


if __name__ == "__main__":
    main()
