import type { AgentRun, RunDetailsResponse } from '@/types/types';

import { generateMockTaskOutput, simulateDelay } from './generators';

/**
 * Mock data for runs by instance
 */
export const getRunsByInstanceMock = async (
  agentChecksum: string
): Promise<AgentRun[]> => {
  await simulateDelay(200, 500);

  const numRuns = Math.floor(Math.random() * 5) + 3; // 3-8 runs
  const mockRuns: AgentRun[] = [];

  for (let i = 0; i < numRuns; i++) {
    const totalTasks = Math.floor(Math.random() * 50) + 20;
    const successCount = Math.floor(totalTasks * (0.6 + Math.random() * 0.3));

    mockRuns.push({
      run_id: `run_${agentChecksum}_${i.toString().padStart(3, '0')}`,
      agent_name: `Instance-${agentChecksum}`,
      timestamp_utc: new Date(
        Date.now() - Math.random() * 7 * 86400000
      ).toISOString(),
      total_tasks: totalTasks,
      success_count: successCount,
      failure_count: totalTasks - successCount,
      dataset_id: `benchmark_${(Math.floor(Math.random() * 3) + 1).toString().padStart(3, '0')}`,
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
 * Mock data for dataset-specific runs
 */
export const getDetailsForDatasetMock = async (
  datasetId: string,
  agentName: string
): Promise<AgentRun[]> => {
  await simulateDelay(200, 500);

  const numRuns = Math.floor(Math.random() * 10) + 5;
  const mockRuns: AgentRun[] = [];

  for (let i = 0; i < numRuns; i++) {
    const totalTasks = Math.floor(Math.random() * 50) + 20;
    const successCount = Math.floor(totalTasks * (0.6 + Math.random() * 0.3));

    mockRuns.push({
      run_id: `run_${agentName}_${i.toString().padStart(3, '0')}_${datasetId}`,
      agent_name: agentName,
      timestamp_utc: new Date(
        Date.now() - Math.random() * 7 * 86400000
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

  const numRuns = Math.floor(Math.random() * 5) + 3;
  const mockRuns: AgentRun[] = [];

  for (let i = 0; i < numRuns; i++) {
    const totalTasks = Math.floor(Math.random() * 50) + 20;
    const successCount = Math.floor(totalTasks * (0.6 + Math.random() * 0.3));

    mockRuns.push({
      run_id: `run_dataset_${datasetId}_${agentChecksum}_${i.toString().padStart(3, '0')}`,
      agent_name: `Instance-${agentChecksum}`,
      timestamp_utc: new Date(
        Date.now() - Math.random() * 7 * 86400000
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
    { agentName: string; uniqueTasks: string[] }
  > = {
    run_agentA_001: {
      agentName: 'agentA',
      uniqueTasks: ['task_A1', 'task_A2', 'task_A3'],
    },
    run_agentB_001: {
      agentName: 'agentB',
      uniqueTasks: ['task_B1', 'task_B2', 'task_B3'],
    },
  };

  const commonTasks = ['task_001', 'task_002', 'task_003'];

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
  taskId: string
): Promise<Record<string, unknown>> => {
  await simulateDelay(300, 600);

  const mockLogs = {
    cpp_code: [
      `// Generated C++ code for ${taskId}\n#include <iostream>\n\nint main() {\n    std::cout << "Hello from ${taskId}" << std::endl;\n    return 0;\n}`,
      `// Alternative implementation\n#include <vector>\n#include <algorithm>\n\nclass Solution {\npublic:\n    void solve() {\n        // Implementation here\n    }\n};`,
    ],
    targetContent: [
      `Target theorem for ${taskId}:\nforall n : nat, n + 0 = n.`,
      `Additional target:\nforall x y : nat, x + y = y + x.`,
    ],
    lemmaContent: [
      `Lemma helper_${taskId.replace('_', '')} : forall n, S n = n + 1.\nProof.\n  induction n.\n  - reflexivity.\n  - simpl. rewrite IHn. reflexivity.\nQed.`,
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
      `[INFO] Starting proof for ${taskId}`,
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
