import argparse
import json
import sys
import uuid
from argparse import ArgumentParser, Namespace
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from observability import add_log_context, get_logger
from rocq_doc_manager import DuneUtil, RocqDocManager

import rocq_pipeline.tasks as Tasks
from rocq_pipeline import loader, locator, util
from rocq_pipeline.agent import Agent, AgentBuilder, Finished, GiveUp, TaskResult
from rocq_pipeline.auto_agent import AutoAgent, OneShotAgent
from rocq_pipeline.locator import Locator
from rocq_pipeline.schema import task_output

logger = get_logger("task_runner")


def mk_parser(parent: Any, with_agent:bool=True) -> Any:
    """
    Extend parent or build a fresh argument parser.
    """
    # Set up the argument parser
    desc = "Run an agent over a collection of tasks"
    if parent:
        parser = parent.add_parser("run", help=desc)
    else:
        parser = ArgumentParser(description=desc)

    if with_agent:
        parser.add_argument('--agent', type=str, help="The agent builder as 'module_path:value', e.g. 'path/to/agent.py:default", required=True)

    # Add the single required positional argument
    parser.add_argument("--task-json", type=json.loads, help="The task descriptor, as JSON.")
    parser.add_argument(
        "--task-file", type=Path, help="The task descriptor in a file, JSON or YAML"
    )
    # Add the optional --trace flag
    parser.add_argument("--trace", action="store_true", help="Enable tracing.")
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("."),
        help="The directory to output task results, as JSONL."
    )
    parser.add_argument(
        "-j", "--jobs",
        type=lambda N: max(1, int(N)),
        default=1,
        help="The number of parallel workers."
    )

    return parser

# def main(agent_type: type[Agent], args: list[str] | None = None) -> bool:
#     pass

@dataclass
class FullTask:
    id: str
    file: Path
    locator: Locator
    rocq_args: list[str]|None
    prompt: str|None


def run_task(build_agent: AgentBuilder, task: FullTask, run_id:str, wdir:Path, progress: util.ProgressCallback) -> task_output.TaskOutput | None:
    """
    Build an agent using [build_agent] and invoke it on the task.
    """
    # Add run_id to log context for this thread
    add_log_context("run_id", run_id)

    task_id: str = task.id
    add_log_context("task_id", task_id)
    # TODO: integrate with opentelemetry, properly instrument the agent
    # framework and derived agents
    trace_id: str | None = None
    timestamp_iso_8601 = datetime.now(UTC).isoformat()

    task_result: TaskResult | None = None
    agent = build_agent(task.prompt)

    try:
        task_file = task.file
        progress(0.01, "🔃")
        with RocqDocManager(
                DuneUtil.rocq_args_for(task_file) if task.rocq_args is None else task.rocq_args,
                str(task_file),
                dune=True,
        ) as rdm:
            progress(0.05, "🔃")
            if not isinstance(rdm.load_file(), RocqDocManager.Resp):
                return None
            progress(0.06, "🔎")

            if not task.locator(rdm):
                print(f"{task_id}: locator returned false")
                return None
            progress(0.1, "💭")
            task_result = agent.run(rdm)
    except Exception as e:
        print(f"Failure with {e}")
        task_result = GiveUp.from_exception(e)
    finally:
        progress(0.95, "🔚")
    assert task_result is not None

    task_failure_reason: task_output.FailureReason | None = None
    if isinstance(task_result, GiveUp):
        task_status = task_output.TaskStatus(task_output.Failure())
        task_failure_reason = task_output.FailureReason(
            task_output.Other(task_result.message)
        )
        print(f"agent gave up with message: {task_result.message}")
    elif isinstance(task_result, Finished):
        task_status = task_output.TaskStatus(task_output.Success())
        print(f"task completed: {task_result.message}")

    return task_output.TaskOutput(
        run_id=run_id,
        task_kind=task.locator.task_kind(),
        task_id=task_id,
        trace_id=trace_id,
        timestamp_utc=timestamp_iso_8601,
        agent_name=agent.name(),
        status=task_status,
        results=task_result.final_doc_interaction,
        failure_reason=task_failure_reason,
        metrics=task_result.metrics,
    )

def load_tasks(arguments: argparse.Namespace) -> tuple[str, Path, list[FullTask]]:
    """
    The path returned here is used to find the build.py file.
    TODO: That should be resolved in here
    """
    if arguments.task_json and arguments.task_file:
        logger.warning(" ".join([
            "[--task-file ...] and [--task-json ...] shouldn't both be used;",
            "choosing [--task-json]."
        ]))

    def to_full_task(raw: dict, wdir: Path) -> FullTask:
        # TODO: find a better name for tasks
        id = f"{raw['file']}#{raw['locator']}"
        file = wdir / raw['file']
        return FullTask(id, file, locator.parse_locator(raw['locator']), None, raw['prompt'] if 'prompt' in raw else None)

    if arguments.task_json is not None:
        tasks = Tasks.mk_validated_tasklist(arguments.task_json)
        wdir = Path('.')
        return ("tasks", wdir, [to_full_task(raw, wdir) for raw in tasks])
    elif arguments.task_file is not None:
        (wdir, tasks) = Tasks.load_tasks(arguments.task_file)
        tasks_name = arguments.task_file.stem
        return (tasks_name, wdir, [to_full_task(raw, wdir) for raw in tasks])
    else:
        raise ValueError("unspecified task")

def load_agent(agent_desc: str) -> AgentBuilder:
    try:
        (agent_mod, agent_type_name) = agent_desc.rsplit(':', maxsplit=1)
    except ValueError:
        agent_mod = agent_desc
        agent_type_name = 'default'
    try:
        mod = loader.load_module(Path(agent_mod))
        result = getattr(mod, agent_type_name)
        if isinstance(result, AgentBuilder):
            return result
        raise Exception(f"{result} is not an [AgentBuilder]")
    except Exception as err:
        raise ValueError(f"Failed to load AgentBuilder from {agent_mod}:{agent_type_name}.") from err

@dataclass
class RunConfiguration:
    agent_builder: AgentBuilder
    tasks: list[FullTask]
    tasks_name: str
    output_dir: Path
    working_dir: Path
    trace: bool
    jobs: int

def parse_arguments(arguments: Namespace, agent_builder:AgentBuilder|None = None) -> RunConfiguration:
    if agent_builder is None:
        if arguments.agent is None:
            raise ValueError("Missing agent configuration. Pass [--agent ...].")
        agent_builder = load_agent(arguments.agent)

    (tasks_name, wdir, tasks) = load_tasks(arguments)

    return RunConfiguration(agent_builder, tasks, tasks_name, arguments.output_dir, wdir, arguments.trace, arguments.jobs)

def run_config(config: RunConfiguration) -> bool:
    def rocq_args(filename: Path) -> list[str]:
        # TODO: a better default
        return DuneUtil.rocq_args_for(filename)

    now_str = datetime.now().strftime("%Y%m%d_%H%M")
    tasks_result_file: Path = (
        config.output_dir / f"{config.tasks_name}_results_{now_str}.jsonl"
    )
    run_id: str = str(uuid.uuid4())
    # Here log context is not getting passed in the multithreads
    # # add_log_context("run_id", run_id)

    def run_it(full_task: FullTask, progress:Any) -> task_output.TaskOutput | None:
        return run_task(config.agent_builder, full_task, run_id, wdir=config.working_dir, progress=progress)

    # Touch the file early to make sure that it is createable
    Path(tasks_result_file).touch()

    def is_success(result: task_output.TaskOutput|None) -> bool:
        return result is not None and str(result.status.value) == 'Success()'

    def succeeded(result: task_output.TaskOutput|None) -> bool:
        if result is None:
            return False
        with open(tasks_result_file, "a", encoding="utf8") as f:
            json.dump(result.to_json(), f)
            f.write("\n")
        return is_success(result)

    results = util.parallel_runner(run_it, [(t.id, t) for t in config.tasks], succeeded=succeeded, jobs=config.jobs)
    # with ThreadPoolExecutor(config.jobs) as tpe:
    #     # NOTE: iterator blocks if the next result has not been yielded
    #     for result in tpe.map(run_it, config.tasks):
    #         if result is not None:
    #             with open(tasks_result_file, "a", encoding="utf8") as f:
    #                 json.dump(result.to_json(), f)
    #                 f.write("\n")

    total = len(results)
    success = len([x for x in results if is_success(x)])

    print(f"Finished {total} tasks: {success} Success, {total-success} Failures")

    return True

def agent_main(agent_builder: AgentBuilder, args: list[str]|None=None) -> bool:
    """
    A simple entry point for an agent to be run as a stand-alone file.

    Clients that use this function should provide an entry point to their agent like:

        def agent_builder(args: list[str]=[], prompt:str|None=None) -> Agent:
            return MyAgent()

        if __name__ == '__main__':
            agent_main(agent_builder)
    """
    if args is None:
        args = sys.argv[1:]
    try:
        idx = args.index('--')
        agent_args:list[str] = args[idx+1:]
        args = args[:idx]
    except ValueError:
        agent_args = []

    arguments: Namespace = mk_parser(parent=None,with_agent=agent_builder is None).parse_args(args)
    config: RunConfiguration = parse_arguments(arguments, agent_builder=agent_builder)
    if agent_args:
        config.agent_builder.add_args(agent_args)

    return run_config(config)

def run_ns(args: Namespace, extra_args:list[str]|None=None) -> bool:
    """Assumes that agent is set"""
    config = parse_arguments(args, None)
    if extra_args:
        config.agent_builder.add_args(extra_args)
    return run_config(config)


def auto_main() -> bool:
    return agent_main(AgentBuilder.of_agent(AutoAgent))

def tactic_main() -> bool:
    class OneShotBuilder(AgentBuilder):
        def __init__(self) -> None:
            self._tactic:str|None = None

        def add_args(self, args:list[str]) -> None:
            if len(args) == 1:
                self._tactic = args[1]
            elif len(args) == 0:
                print("Missing tactic argument")
            else:
                print("Too many tactics given")

        def __call__(self, prompt:str|None=None) -> Agent:
            if self._tactic is None:
                print("Missing tactic argument")
                raise ValueError("Missing tactic argument")
            return OneShotAgent(self._tactic)

    return agent_main(OneShotBuilder())
