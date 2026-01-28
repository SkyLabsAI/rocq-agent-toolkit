import type {
  AgentRun,
  RunDetailsResponse,
  TaskDetailsResponse,
  TaskOutput,
} from '@/types/types';

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

  console.log(taskId);
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

/**
 * Mock bulk add tags operation
 */
export const bulkAddTagsMock = async (request: {
  task_ids: number[];
  tags: string[];
}): Promise<{
  success: boolean;
  message: string;
  tasks_updated: number;
  tags_added: number;
}> => {
  await simulateDelay(300, 600);

  const { task_ids, tags } = request;
  const tasksUpdated = task_ids.length;
  const tagsAdded = tags.length * tasksUpdated; // Each tag is added to each task

  const mockResponse = {
    success: true,
    message: `Successfully added ${tags.length} tag(s) to ${tasksUpdated} task(s)`,
    tasks_updated: tasksUpdated,
    tags_added: tagsAdded,
  };

  console.log('Bulk add tags response (MOCK):', mockResponse);
  return mockResponse;
};

/**
 * Mock data for task details by task ID
 */
export const getTaskDetailsByIdMock = async (
  taskId: number
): Promise<TaskDetailsResponse> => {
  await simulateDelay(200, 400);

  const mockTask: TaskDetailsResponse = {
    task_id: taskId,
    task_name: `task_${taskId.toString().padStart(3, '0')}`,
    task_kind: 'FullProofTask',
    dataset_id: `dataset_${taskId.toString().padStart(3, '0')}`,
    dataset: {
      dataset_id: `dataset_${taskId.toString().padStart(3, '0')}`,
      description: `Mock dataset for task ${taskId}`,
      created_at: new Date().toISOString(),
    },
    ground_truth: `forall n : nat, n + 0 = n.

Proof:
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.`,
    tags: {
      category: 'algebra',
      difficulty: 'easy',
      status: 'active',
    },
  };

  console.log(`Fetched task details for task ${taskId} (MOCK):`, mockTask);
  return mockTask;
};

/**
 * Mock data for latest runs
 */
export const getLatestRunsMock = async (limit: number = 10): Promise<AgentRun[]> => {
  await simulateDelay(300, 600);

  // Predefined realistic run data
  const predefinedRuns: AgentRun[] = [
    {
      run_id: 'bc9a4757-74b5-4fae-a9b4-97a1eecdb665',
      agent_name: 'GPT4TacticAgent',
      timestamp_utc: new Date(Date.now() - 1 * 3600000).toISOString(), // 1 hour ago
      total_tasks: 45,
      success_count: 42,
      failure_count: 3,
      dataset_id: 'mathlib_algebra',
      metadata: {
        tags: {
          version: 'v2.1',
          model: 'gpt-4-turbo',
          environment: 'production',
          priority: 'high',
        },
      },
    },
    {
      run_id: '6169bedd-e162-4238-9a18-7fba40fa5aa4',
      agent_name: 'ClaudeProofAgent',
      timestamp_utc: new Date(Date.now() - 2.5 * 3600000).toISOString(), // 2.5 hours ago
      total_tasks: 38,
      success_count: 35,
      failure_count: 3,
      dataset_id: 'software_foundations',
      metadata: {
        tags: {
          version: 'v2.0',
          model: 'claude-3-opus',
          environment: 'production',
        },
      },
    },
    {
      run_id: 'a7f3c891-22e4-4b9a-b123-45678def9012',
      agent_name: 'MistralReasoningAgent',
      timestamp_utc: new Date(Date.now() - 4 * 3600000).toISOString(), // 4 hours ago
      total_tasks: 50,
      success_count: 38,
      failure_count: 12,
      dataset_id: 'lean_benchmark',
      metadata: {
        tags: {
          version: 'v1.9',
          model: 'mistral-large',
          environment: 'staging',
          priority: 'medium',
        },
      },
    },
    {
      run_id: 'f9b2e3d4-5678-4abc-9def-012345678abc',
      agent_name: 'GPT4TacticAgent',
      timestamp_utc: new Date(Date.now() - 6 * 3600000).toISOString(), // 6 hours ago
      total_tasks: 42,
      success_count: 40,
      failure_count: 2,
      dataset_id: 'mathlib_topology',
      metadata: {
        tags: {
          version: 'v2.1',
          model: 'gpt-4-turbo',
          environment: 'production',
          experiment: 'baseline',
        },
      },
    },
    {
      run_id: 'e1234567-89ab-cdef-0123-456789abcdef',
      agent_name: 'LlamaCoqAgent',
      timestamp_utc: new Date(Date.now() - 8 * 3600000).toISOString(), // 8 hours ago
      total_tasks: 30,
      success_count: 18,
      failure_count: 12,
      dataset_id: 'coq_stdlib',
      metadata: {
        tags: {
          version: 'v1.5',
          model: 'llama-3-70b',
          environment: 'development',
          priority: 'low',
        },
      },
    },
    {
      run_id: 'c9876543-21fe-dcba-9876-543210fedcba',
      agent_name: 'GeminiProofAgent',
      timestamp_utc: new Date(Date.now() - 10 * 3600000).toISOString(), // 10 hours ago
      total_tasks: 35,
      success_count: 32,
      failure_count: 3,
      dataset_id: 'mathlib_algebra',
      metadata: {
        tags: {
          version: 'v1.8',
          model: 'gemini-pro',
          environment: 'production',
        },
      },
    },
    {
      run_id: 'd4567890-abcd-ef12-3456-7890abcdef12',
      agent_name: 'ClaudeProofAgent',
      timestamp_utc: new Date(Date.now() - 12 * 3600000).toISOString(), // 12 hours ago
      total_tasks: 48,
      success_count: 44,
      failure_count: 4,
      dataset_id: 'software_foundations',
      metadata: {
        tags: {
          version: 'v2.0',
          model: 'claude-3-opus',
          environment: 'production',
          priority: 'high',
          experiment: 'optimized',
        },
      },
    },
    {
      run_id: 'b7890123-4567-89ab-cdef-0123456789ab',
      agent_name: 'GPT4TacticAgent',
      timestamp_utc: new Date(Date.now() - 15 * 3600000).toISOString(), // 15 hours ago
      total_tasks: 40,
      success_count: 38,
      failure_count: 2,
      dataset_id: 'lean_benchmark',
      metadata: {
        tags: {
          version: 'v2.0',
          model: 'gpt-4',
          environment: 'staging',
        },
      },
    },
    {
      run_id: 'a2345678-90ab-cdef-0123-456789012345',
      agent_name: 'MistralReasoningAgent',
      timestamp_utc: new Date(Date.now() - 18 * 3600000).toISOString(), // 18 hours ago
      total_tasks: 44,
      success_count: 26,
      failure_count: 18,
      dataset_id: 'mathlib_topology',
      metadata: {
        tags: {
          version: 'v1.9',
          model: 'mistral-medium',
          environment: 'development',
          priority: 'low',
        },
      },
    },
    {
      run_id: '98765432-10fe-dcba-9876-543210fedcba',
      agent_name: 'LlamaCoqAgent',
      timestamp_utc: new Date(Date.now() - 20 * 3600000).toISOString(), // 20 hours ago
      total_tasks: 28,
      success_count: 22,
      failure_count: 6,
      dataset_id: 'coq_stdlib',
      metadata: {
        tags: {
          version: 'v1.6',
          model: 'llama-3-70b',
          environment: 'production',
          experiment: 'cot',
        },
      },
    },
    {
      run_id: '87654321-0fed-cba9-8765-4321fedcba98',
      agent_name: 'GeminiProofAgent',
      timestamp_utc: new Date(Date.now() - 22 * 3600000).toISOString(), // 22 hours ago
      total_tasks: 36,
      success_count: 33,
      failure_count: 3,
      dataset_id: 'software_foundations',
      metadata: {
        tags: {
          version: 'v1.8',
          model: 'gemini-ultra',
          environment: 'production',
          priority: 'high',
        },
      },
    },
    {
      run_id: '76543210-fedc-ba98-7654-321fedcba987',
      agent_name: 'ClaudeProofAgent',
      timestamp_utc: new Date(Date.now() - 24 * 3600000).toISOString(), // 24 hours ago
      total_tasks: 41,
      success_count: 39,
      failure_count: 2,
      dataset_id: 'mathlib_algebra',
      metadata: {
        tags: {
          version: 'v2.1',
          model: 'claude-3-sonnet',
          environment: 'production',
        },
      },
    },
  ];

  // Return the requested number of runs
  const runsToReturn = predefinedRuns.slice(0, Math.min(limit, predefinedRuns.length));

  console.log(`Fetched ${runsToReturn.length} latest runs (MOCK)`, runsToReturn);
  return runsToReturn;
};
