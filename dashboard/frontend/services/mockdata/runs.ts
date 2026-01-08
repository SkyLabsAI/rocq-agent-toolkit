import type { AgentRun, RunDetailsResponse, TaskOutput } from '@/types/types';

import { generateMockTaskOutput, simulateDelay } from './generators';

/**
 * Mock data for runs by instance
 */
export const getRunsByInstanceMock = async (
  agentChecksum: string
): Promise<AgentRun[]> => {
  await simulateDelay(200, 500);

  const numRuns = 5; // Fixed: always return 5 runs
  const mockRuns: AgentRun[] = [];

  for (let i = 0; i < numRuns; i++) {
    const totalTasks = 28 + i * 4; // Fixed: 28, 32, 36, 40, 44
    const successCount = Math.floor(totalTasks * 0.72); // Fixed: 72% success rate

    mockRuns.push({
      run_id: `run_${agentChecksum}_${i.toString().padStart(3, '0')}`,
      agent_name: `Instance-${agentChecksum}`,
      timestamp_utc: new Date(
        Date.now() - (i + 1) * 1.5 * 86400000 // Fixed: 1.5, 3, 4.5, 6, 7.5 days ago
      ).toISOString(),
      total_tasks: totalTasks,
      success_count: successCount,
      failure_count: totalTasks - successCount,
      dataset_id: `benchmark_${((i % 3) + 1).toString().padStart(3, '0')}`, // Fixed: cycles through benchmark_001, 002, 003
      metadata: {
        tags: {
          run_id: `run_${agentChecksum}_${i.toString().padStart(3, '0')}`,
        },
      },
    });
  }

  console.log(
    `Fetched ${mockRuns.length} runs for instance ${agentChecksum} (MOCK)`,
    mockRuns
  );
  return mockRuns;
};

/**
 * Mock data for agent instance task runs
 */
export const getAgentInstanceTaskRunsMock = async (
  agentChecksum: string,
  taskId: number
): Promise<AgentRun[]> => {
  await simulateDelay(200, 500);
  // Filter runs to only include those that would have this task
  const allRuns = await getRunsByInstanceMock(agentChecksum);
  // Return first 3 runs as mock (simulating filtered results)
  return allRuns.filter((_, index) => index < 3);
};

/**
 * Mock data for dataset-specific runs
 */
export const getDetailsForDatasetMock = async (
  datasetId: string,
  agentName: string
): Promise<AgentRun[]> => {
  await simulateDelay(200, 500);

  const numRuns = 7; // Fixed: always return 7 runs
  const mockRuns: AgentRun[] = [];

  for (let i = 0; i < numRuns; i++) {
    const totalTasks = 22 + i * 6; // Fixed: 22, 28, 34, 40, 46, 52, 58
    const successCount = Math.floor(totalTasks * 0.68); // Fixed: 68% success rate

    mockRuns.push({
      run_id: `run_${agentName}_${i.toString().padStart(3, '0')}_${datasetId}`,
      agent_name: agentName,
      timestamp_utc: new Date(
        Date.now() - (i + 1) * 2 * 86400000 // Fixed: 2, 4, 6, 8, 10, 12, 14 days ago
      ).toISOString(),
      total_tasks: totalTasks,
      success_count: successCount,
      failure_count: totalTasks - successCount,
      dataset_id: datasetId,
      metadata: {
        tags: {
          dataset_id: datasetId,
          run_id: `run_${agentName}_${i.toString().padStart(3, '0')}`,
          task_id: `task_${agentName}_${i.toString().padStart(3, '0')}`,
          hehe: 'hehe',
          somethingelse: 'somethingelse',
        },
      },
    });
  }

  console.log(
    `Fetched runs for agent ${agentName} in dataset ${datasetId} (MOCK):`,
    mockRuns
  );
  return mockRuns;
};

/**
 * Mock data for dataset instance runs
 */
export const getDatasetInstanceRunsMock = async (
  datasetId: string,
  agentChecksum: string
): Promise<AgentRun[]> => {
  await simulateDelay(200, 500);

  const numRuns = 4; // Fixed: always return 4 runs
  const mockRuns: AgentRun[] = [];

  for (let i = 0; i < numRuns; i++) {
    const totalTasks = 26 + i * 7; // Fixed: 26, 33, 40, 47
    const successCount = Math.floor(totalTasks * 0.76); // Fixed: 76% success rate

    mockRuns.push({
      run_id: `run_dataset_${datasetId}_${agentChecksum}_${i.toString().padStart(3, '0')}`,
      agent_name: `Instance-${agentChecksum}`,
      timestamp_utc: new Date(
        Date.now() - (i + 1) * 2.5 * 86400000 // Fixed: 2.5, 5, 7.5, 10 days ago
      ).toISOString(),
      total_tasks: totalTasks,
      success_count: successCount,
      failure_count: totalTasks - successCount,
      dataset_id: datasetId,
      metadata: {
        tags: {
          run_id: `run_dataset_${datasetId}_${agentChecksum}_${i.toString().padStart(3, '0')}`,
          dataset: datasetId,
        },
      },
    });
  }

  console.log(
    `Fetched ${mockRuns.length} runs for dataset ${datasetId}, instance ${agentChecksum} (MOCK)`,
    mockRuns
  );
  return mockRuns;
};

/**
 * Mock data for detailed run information (used for comparisons)
 */
export const getRunDetailsMock = async (
  runIds: string[]
): Promise<RunDetailsResponse[]> => {
  await simulateDelay(500, 1000);

  // For this mock, we'll support agentA and agentB
  // Each has 6 tasks: 3 common (task_001, task_002, task_003), 3 unique
  const agentRunMap: Record<
    string,
    { agentName: string; uniqueTasks: number[] }
  > = {
    run_agentA_001: {
      agentName: 'agentA',
      uniqueTasks: [1, 2, 3],
    },
    run_agentB_001: {
      agentName: 'agentB',
      uniqueTasks: [4, 5, 6],
    },
  };

  const commonTasks = [1, 2, 3];

  const mockRunDetails: RunDetailsResponse[] = runIds.map(runId => {
    const agentInfo = agentRunMap[runId] || {
      agentName: 'UnknownAgent',
      uniqueTasks: [],
    };
    const tasks = [];

    // Add common tasks
    for (let i = 0; i < commonTasks.length; i++) {
      tasks.push({
        ...generateMockTaskOutput(runId, agentInfo.agentName, i),
        task_id: commonTasks[i],
      });
    }

    // Add unique tasks
    for (let i = 0; i < agentInfo.uniqueTasks.length; i++) {
      tasks.push({
        ...generateMockTaskOutput(runId, agentInfo.agentName, i + 10),
        task_id: agentInfo.uniqueTasks[i],
      });
    }

    return {
      run_id: runId,
      agent_name: agentInfo.agentName,
      total_tasks: tasks.length,
      tasks,
    };
  });

  console.log('Fetched run details (MOCK):', mockRunDetails);
  return mockRunDetails;
};

/**
 * Mock data for observability logs (tactic info, proofs, etc.)
 */
export const getObservabilityLogsMock = async (
  runId: string,
  taskId: number
): Promise<Record<string, unknown>> => {
  await simulateDelay(300, 600);

  const taskIdStr = String(taskId);
  const mockLogs = {
    cpp_code: [
      `// Generated C++ code for ${taskIdStr}\n#include <iostream>\n\nint main() {\n    std::cout << "Hello from ${taskIdStr}" << std::endl;\n    return 0;\n}`,
      `// Alternative implementation\n#include <vector>\n#include <algorithm>\n\nclass Solution {\npublic:\n    void solve() {\n        // Implementation here\n    }\n};`,
    ],
    targetContent: [
      `Target theorem for ${taskIdStr}:\nforall n : nat, n + 0 = n.`,
      `Additional target:\nforall x y : nat, x + y = y + x.`,
    ],
    lemmaContent: [
      `Lemma helper_${taskIdStr.replace('_', '')} : forall n, S n = n + 1.\nProof.\n  induction n.\n  - reflexivity.\n  - simpl. rewrite IHn. reflexivity.\nQed.`,
    ],
    statesContent: [
      `Initial state: Goal (forall n, n + 0 = n)\nTactic applied: induction n\nSubgoal 1: 0 + 0 = 0\nSubgoal 2: forall n, n + 0 = n -> S n + 0 = S n`,
    ],
    tactic: [
      {
        name: 'induction',
        tactic_prediction_tactic: 'induction n.',
        status: 'Success' as const,
        tactic_prediction_explanation:
          'Apply mathematical induction on the variable n to break down the proof into base case and inductive step',
        complexity_score: 7,
        confidence: 0.89,
        execution_time_ms: 145,
      },
      {
        name: 'reflexivity',
        tactic_prediction_tactic: 'reflexivity.',
        status: 'Success' as const,
        tactic_prediction_explanation:
          'Use reflexivity to prove that 0 + 0 = 0, which is true by definition',
        complexity_score: 2,
        confidence: 0.98,
        execution_time_ms: 23,
      },
      {
        name: 'simpl_rewrite',
        tactic_prediction_tactic: 'simpl. rewrite IHn. reflexivity.',
        status: 'failure' as const,
        tactic_prediction_explanation:
          'Attempt to simplify and rewrite using inductive hypothesis, but failed due to context mismatch',
        complexity_score: 5,
        confidence: 0.65,
        execution_time_ms: 98,
        error_message: 'Unable to apply rewrite rule in current context',
      },
      {
        name: 'auto',
        tactic_prediction_tactic: 'auto.',
        status: 'Success' as const,
        tactic_prediction_explanation:
          'Automatic solver successfully completes the remaining proof obligations',
        complexity_score: 1,
        confidence: 0.95,
        execution_time_ms: 67,
        fallback_tactics: ['trivial', 'omega', 'lia'],
      },
    ],
    tactic_prediction_explanation: [
      `Step 1: Analyze the goal structure`,
      `Step 2: Identify induction pattern`,
      `Step 3: Apply induction tactic`,
      `Step 4: Solve base case with reflexivity`,
      `Step 5: Solve inductive step using hypothesis`,
    ],
    tactic_prediction_tactic: [
      `induction n.`,
      `- reflexivity.`,
      `- simpl. rewrite IHn. reflexivity.`,
    ],
    proof_steps: [
      `1. Start with goal: forall n : nat, n + 0 = n`,
      `2. Apply induction on n`,
      `3. Base case: 0 + 0 = 0 (by definition)`,
      `4. Inductive step: assume n + 0 = n, prove S n + 0 = S n`,
      `5. Simplify S n + 0 to S (n + 0)`,
      `6. Rewrite using inductive hypothesis`,
      `7. QED`,
    ],
    execution_log: [
      `[INFO] Starting proof for ${taskIdStr}`,
      `[DEBUG] Parsing goal structure`,
      `[INFO] Applying tactic: induction n`,
      `[DEBUG] Generated subgoals: 2`,
      `[INFO] Solving base case`,
      `[INFO] Solving inductive step`,
      `[SUCCESS] Proof completed`,
    ],
    metadata: {
      run_id: runId,
      task_id: taskId,
      generated_at: new Date().toISOString(),
      agent_version: 'mock_v1.0',
    },
  };

  console.log('Fetched observability logs (MOCK):', mockLogs);
  return mockLogs;
};

/**
 * Mock refresh data operation
 */
export const refreshDataMock = async (): Promise<{
  success: boolean;
  message: string;
  total_tasks: number;
  total_agents: number;
}> => {
  await simulateDelay(800, 1500);

  const mockRefreshResponse = {
    success: true,
    message: 'Mock data refreshed successfully',
    total_tasks: Math.floor(Math.random() * 1000) + 500,
    total_agents: Math.floor(Math.random() * 10) + 5,
  };

  console.log('Refresh response (MOCK):', mockRefreshResponse);
  return mockRefreshResponse;
};

/**
 * Mock data for task details within a specific run
 */
export const getTaskDetailsMock = async (
  runId: string,
  taskId: number
): Promise<TaskOutput> => {
  await simulateDelay(200, 400);

  // Extract task index from taskId if possible, otherwise use a hash
  const taskIndex = taskId;

  // Extract agent name from runId or use default
  const agentName =
    runId.match(/run_(.+?)_/)?.[1] || runId.split('_')[1] || 'UnknownAgent';

  const mockTask = generateMockTaskOutput(runId, agentName, taskIndex);
  mockTask.task_id = taskId;

  console.log(
    `Fetched task details for run ${runId}, task ${taskId} (MOCK):`,
    mockTask
  );
  return mockTask;
};
