"""
Data access layer for querying JSONL task results.
This module provides an abstraction layer that can be easily replaced
with database queries in the future.
"""
import json
import math
from collections import defaultdict
from pathlib import Path

from backend.models import (
    AgentInfo,
    RunDetailsResponse,
    RunInfo,
    TagsResponse,
    TaskMetadata,
    TaskResult,
)


class DataStore:
    """In-memory data store for task results."""

    def __init__(self) -> None:
        """Initialize empty data store."""
        self.task_results: list[TaskResult] = []
        self._indexed = False

        # Indexes for efficient queries
        self._agents: set[str] = set()
        self._runs_by_agent: dict[str, set[str]] = defaultdict(set)
        self._tasks_by_run: dict[str, list[TaskResult]] = defaultdict(list)
        # Metadata tag index: key -> set of unique string values
        self._tags_index: dict[str, set[str]] = defaultdict(set)
        # Derived run-level metrics, keyed by run_id
        self._runs: dict[str, RunInfo] = {}
        # Best-scoring run per agent (maps agent_name -> run_id)
        self._best_run_by_agent: dict[str, str] = {}

    def load_from_directory(self, directory: Path, clear_existing: bool = False) -> int:
        """
        Load all JSONL files from the specified directory.

        Args:
            directory: Path to directory containing JSONL files
            clear_existing: If True, clear existing data before loading

        Returns:
            Number of task results loaded
        """
        if not directory.exists():
            raise FileNotFoundError(f"Directory not found: {directory}")

        if not directory.is_dir():
            raise ValueError(f"Path is not a directory: {directory}")

        # Clear existing data if requested
        if clear_existing:
            self.task_results.clear()

        loaded_count = 0
        parse_error_count = 0

        # Find all JSONL files in the directory
        jsonl_files = list(directory.glob("*.jsonl"))

        for jsonl_file in jsonl_files:
            try:
                with open(jsonl_file, encoding="utf-8") as f:
                    for line_num, line in enumerate(f, 1):
                        line = line.strip()
                        if not line:
                            continue

                        try:
                            data = json.loads(line)
                            task_result = TaskResult(**data)
                            self.task_results.append(task_result)
                            loaded_count += 1
                        except json.JSONDecodeError as e:
                            parse_error_count += 1
                            print(
                                f"Warning: Invalid JSON in {jsonl_file} at line {line_num}: {e}"
                            )
                        except Exception as e:
                            parse_error_count += 1
                            print(
                                f"Warning: Failed to parse entry in {jsonl_file} at line {line_num}: {e}"
                            )

            except Exception as e:
                print(f"Error reading file {jsonl_file}: {e}")

        print(f"Loaded {loaded_count} task results")
        print(f"Parse errors: {parse_error_count}")
        # Build indexes after loading
        self._build_indexes()

        return loaded_count

    def reload_from_directory(self, directory: Path) -> int:
        """
        Reload all JSONL files, clearing existing data first.

        Args:
            directory: Path to directory containing JSONL files

        Returns:
            Number of task results loaded
        """
        return self.load_from_directory(directory, clear_existing=True)

    def _build_indexes(self) -> None:
        """Build internal indexes for efficient querying."""
        self._agents.clear()
        self._runs_by_agent.clear()
        self._tasks_by_run.clear()
        self._tags_index.clear()
        self._runs.clear()
        self._best_run_by_agent.clear()

        for task in self.task_results:
            self._agents.add(task.agent_name)
            self._runs_by_agent[task.agent_name].add(task.run_id)
            self._tasks_by_run[task.run_id].append(task)

            # Index metadata tags if present
            if task.metadata and task.metadata.tags:
                for key, value in task.metadata.tags.items():
                    # Ensure we always store string values for consistency
                    self._tags_index[key].add(str(value))

        # Compute derived per-run metrics and best run per agent
        for run_id, tasks in self._tasks_by_run.items():
            if not tasks:
                continue

            total_tasks = len(tasks)
            success_count = sum(1 for task in tasks if task.status == "Success")
            failure_count = sum(1 for task in tasks if task.status == "Failure")
            earliest_timestamp = min(task.timestamp_utc for task in tasks)
            success_rate = success_count / total_tasks if total_tasks else 0.0

            # Simple scoring heuristic: success rate weighted by number of tasks
            weight = math.log(1 + total_tasks)
            score = success_rate * weight


            # Average metrics across tasks in the run
            total_tokens_list: list[int] = []
            cpu_time_list: list[float] = []

            for task in tasks:
                try:
                    total_tokens_list.append(task.metrics.token_counts.total_tokens)
                except Exception:
                    # If metrics are missing or malformed, skip this task for averages
                    pass

                try:
                    cpu_time_list.append(task.metrics.resource_usage.cpu_time_sec)
                except Exception:
                    pass

            avg_total_tokens = (
                sum(total_tokens_list) / len(total_tokens_list)
                if total_tokens_list
                else 0.0
            )
            avg_cpu_time_sec = (
                sum(cpu_time_list) / len(cpu_time_list) if cpu_time_list else 0.0
            )

            # Build a single RunInfo object per run_id and store it
            run_info = RunInfo(
                run_id=run_id,
                agent_name=tasks[0].agent_name,
                timestamp_utc=earliest_timestamp,
                total_tasks=total_tasks,
                success_count=success_count,
                failure_count=failure_count,
                success_rate=success_rate,
                score=score,
                avg_total_tokens=avg_total_tokens,
                avg_cpu_time_sec=avg_cpu_time_sec,
                metadata=tasks[0].metadata
                if tasks[0].metadata
                else TaskMetadata(),
            )
            self._runs[run_id] = run_info

            # Track best run per agent using the stored RunInfo
            agent_name = run_info.agent_name
            prev_best_run_id = self._best_run_by_agent.get(agent_name)
            if prev_best_run_id is None:
                self._best_run_by_agent[agent_name] = run_id
            else:
                prev_best_run = self._runs.get(prev_best_run_id)
                if prev_best_run is None or run_info.score > prev_best_run.score:
                    self._best_run_by_agent[agent_name] = run_id

        self._indexed = True

    def get_all_agents(self) -> list[AgentInfo]:
        """
        Get list of all unique agents with their run counts.

        Returns:
            List of AgentInfo objects
        """
        agents = []
        for agent_name in sorted(self._agents):
            run_count = len(self._runs_by_agent[agent_name])
            best_run_id = self._best_run_by_agent.get(agent_name)
            best_run = self._runs.get(best_run_id) if best_run_id else None

            agents.append(
                AgentInfo(agent_name=agent_name, total_runs=run_count, best_run=best_run)
            )
        return agents

    def get_runs_by_agent(self, agent_name: str) -> list[RunInfo]:
        """
        Get all runs for a specific agent.

        Args:
            agent_name: Name of the agent

        Returns:
            List of RunInfo objects for the agent
        """
        if agent_name not in self._agents:
            return []

        run_ids = self._runs_by_agent[agent_name]
        runs = []

        for run_id in sorted(run_ids):
            run_info = self._runs.get(run_id)
            if run_info is None:
                continue
            runs.append(run_info)

        # Sort by timestamp (most recent first)
        runs.sort(key=lambda x: x.timestamp_utc, reverse=True)

        return runs

    def get_run_details(self, run_ids: list[str]) -> list[RunDetailsResponse]:
        """
        Get complete details for one or more runs.

        Args:
            run_ids: List of run IDs to retrieve

        Returns:
            List of RunDetailsResponse objects
        """
        results = []

        for run_id in run_ids:
            tasks = self._tasks_by_run.get(run_id, [])

            if not tasks:
                continue

            # All tasks in a run should have the same agent_name
            agent_name = tasks[0].agent_name if tasks else "Unknown"

            results.append(
                RunDetailsResponse(
                    run_id=run_id,
                    agent_name=agent_name,
                    total_tasks=len(tasks),
                    tasks=sorted(tasks, key=lambda x: x.timestamp_utc),
                )
            )

        return results

    def get_unique_tags(self) -> TagsResponse:
        """
        Get all unique metadata tag keys and their unique values across tasks.

        Returns:
            TagsResponse containing a mapping from tag key to sorted list of values.
        """
        tags: dict[str, list[str]] = {
            key: sorted(values) for key, values in self._tags_index.items()
        }

        total_keys = len(tags)
        total_values = sum(len(values) for values in tags.values())

        return TagsResponse(tags=tags, total_keys=total_keys, total_values=total_values)


# Global data store instance
data_store = DataStore()
