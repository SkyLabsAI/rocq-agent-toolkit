"""
Data access layer for querying JSONL task results.
This module provides an abstraction layer that can be easily replaced
with database queries in the future.
"""
import json
from pathlib import Path
from typing import List, Dict, Set
from collections import defaultdict

from backend.models import (
    TaskMetadata,
    TaskResult,
    AgentInfo,
    RunInfo,
    RunDetailsResponse,
    TagsResponse,
)


class DataStore:
    """In-memory data store for task results."""

    def __init__(self) -> None:
        """Initialize empty data store."""
        self.task_results: List[TaskResult] = []
        self._indexed = False

        # Indexes for efficient queries
        self._agents: Set[str] = set()
        self._runs_by_agent: Dict[str, Set[str]] = defaultdict(set)
        self._tasks_by_run: Dict[str, List[TaskResult]] = defaultdict(list)
        # Metadata tag index: key -> set of unique string values
        self._tags_index: Dict[str, Set[str]] = defaultdict(set)

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

        # Find all JSONL files in the directory
        jsonl_files = list(directory.glob("*.jsonl"))

        for jsonl_file in jsonl_files:
            try:
                with open(jsonl_file, "r", encoding="utf-8") as f:
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
                            print(
                                f"Warning: Invalid JSON in {jsonl_file} at line {line_num}: {e}"
                            )
                        except Exception as e:
                            print(
                                f"Warning: Failed to parse entry in {jsonl_file} at line {line_num}: {e}"
                            )

            except Exception as e:
                print(f"Error reading file {jsonl_file}: {e}")

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

        for task in self.task_results:
            self._agents.add(task.agent_name)
            self._runs_by_agent[task.agent_name].add(task.run_id)
            self._tasks_by_run[task.run_id].append(task)

            # Index metadata tags if present
            if task.metadata and task.metadata.tags:
                for key, value in task.metadata.tags.items():
                    # Ensure we always store string values for consistency
                    self._tags_index[key].add(str(value))

        self._indexed = True

    def get_all_agents(self) -> List[AgentInfo]:
        """
        Get list of all unique agents with their run counts.

        Returns:
            List of AgentInfo objects
        """
        agents = []
        for agent_name in sorted(self._agents):
            run_count = len(self._runs_by_agent[agent_name])
            agents.append(AgentInfo(agent_name=agent_name, total_runs=run_count))
        return agents

    def get_runs_by_agent(self, agent_name: str) -> List[RunInfo]:
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
            tasks = self._tasks_by_run[run_id]
            if not tasks:
                continue

            # Get earliest timestamp for this run
            earliest_timestamp = min(task.timestamp_utc for task in tasks)

            # Count successes and failures
            success_count = sum(1 for task in tasks if task.status == "Success")
            failure_count = sum(1 for task in tasks if task.status == "Failure")

            runs.append(
                RunInfo(
                    run_id=run_id,
                    agent_name=agent_name,
                    timestamp_utc=earliest_timestamp,
                    total_tasks=len(tasks),
                    success_count=success_count,
                    failure_count=failure_count,
                    metadata=tasks[0].metadata if tasks[0].metadata else TaskMetadata(),
                )
            )

        # Sort by timestamp (most recent first)
        runs.sort(key=lambda x: x.timestamp_utc, reverse=True)

        return runs

    def get_run_details(self, run_ids: List[str]) -> List[RunDetailsResponse]:
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
        tags: Dict[str, List[str]] = {
            key: sorted(values) for key, values in self._tags_index.items()
        }

        total_keys = len(tags)
        total_values = sum(len(values) for values in tags.values())

        return TagsResponse(tags=tags, total_keys=total_keys, total_values=total_values)


# Global data store instance
data_store = DataStore()
