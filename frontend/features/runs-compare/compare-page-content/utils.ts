import { RunDetailsResponse, TaskOutput } from "@/types/types";
import { RunStats } from "..";

export const computeRunStats = (run: RunDetailsResponse): RunStats => {
  const tasks = run.tasks.length;
  const successes = run.tasks.filter(t => t.status === 'Success').length;
  return {
    id: run.run_id,
    name: run.agent_name,
    tasks,
    successRate: tasks === 0 ? 0 : successes / tasks,
    totalLlmCalls: run.tasks.reduce(
      (a, t) => a + (t.metrics?.llm_invocation_count),
      0
    ),
    totalTokens: run.tasks.reduce(
      (a, t) => a + (t.metrics?.token_counts?.total_tokens),
      0
    ),
    avgExecutionTime:
      tasks === 0
        ? 0
        : run.tasks.reduce(
            (a, t) => a + (t.metrics?.resource_usage?.execution_time_sec),
            0
          ) / tasks,
  };
};

const normalizeFailureReason = (fr: unknown): string => {
  if (fr == null) return '';
  if (Array.isArray(fr)) {
    return fr
      .map(x => (typeof x === 'string' ? x : JSON.stringify(x)))
      .join(' | ');
  }
  if (typeof fr === 'object') {
    const obj = fr as { kind?: string; value?: unknown };
    if (obj.kind) {
      return (
        obj.kind +
        (obj.value
          ? ': ' +
            (typeof obj.value === 'object'
              ? JSON.stringify(obj.value)
              : String(obj.value))
          : '')
      );
    }
    return JSON.stringify(fr);
  }
  return String(fr);
};




export interface TaskRowData {
  taskId: string;
  cells: Array<{
    runId: string;
    runName: string;
    task: TaskOutput 
  }>;
}

export function transformRunsToTaskRows(runs: RunDetailsResponse[]): TaskRowData[] {
  const taskMap = new Map<string, TaskRowData>();

  // 1. Iterate through every run (Column)
  runs.forEach((run, runIndex) => {
    
    // 2. Iterate through every task in this run
    run.tasks.forEach((task) => {
      const taskId = task.task_id;

      // If this is the first time we see this Task ID, initialize the row
      if (!taskMap.has(taskId)) {
        taskMap.set(taskId, {
          taskId: taskId,
          // Create an array full of NULLs, length = number of runs
          // This guarantees grid alignment
          cells: new Array(runs.length).fill(null)
        });
      }

      // 3. Place the data in the correct slot (runIndex)
      const row = taskMap.get(taskId)!;
      row.cells[runIndex] = {
        runId: run.run_id,
        runName: run.agent_name || run.run_id,
        task: task
      };
    });
  });

  // Convert Map to Array and Sort by Task ID
  return Array.from(taskMap.values()).sort((a, b) => 
    a.taskId.localeCompare(b.taskId)
  );
}