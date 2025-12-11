import axios from 'axios';

import { config } from '@/config/env';
import {
  type AgentRun,
  type AgentSummary,
  type Benchmark,
  type RunDetailsResponse,
  type TaskOutput,
} from '@/types/types';

// Check if we should use mock data
const USE_MOCK_DATA = config.USE_MOCK_DATA;

// Mock data generator functions
const generateMockTaskOutput = (
  runId: string,
  agentName: string,
  taskIndex: number
): TaskOutput => {
  const isSuccess = Math.random() > 0.3; // 70% success rate
  const taskId = `task_${taskIndex.toString().padStart(3, '0')}`;

  return {
    run_id: runId,
    task_kind: 'FullProofTask',
    task_id: taskId,
    trace_id: `trace_${Math.random().toString(36).substring(2, 15)}`,
    timestamp_utc: new Date(
      Date.now() - Math.random() * 86400000
    ).toISOString(),
    agent_name: agentName,
    status: isSuccess ? 'Success' : 'Failure',
    failure_reason: !isSuccess
      ? [
          'Proof step failed during execution',
          'Timeout exceeded after 30 seconds',
          'Unable to find valid tactic sequence',
        ]
      : undefined,
    results: {
      proof_found: isSuccess,
      steps_taken: Math.floor(Math.random() * 50) + 1,
    },
    metrics: {
      llm_invocation_count: Math.floor(Math.random() * 20) + 5,
      token_counts: {
        input_tokens: Math.floor(Math.random() * 5000) + 1000,
        output_tokens: Math.floor(Math.random() * 2000) + 500,
        total_tokens: Math.floor(Math.random() * 7000) + 1500,
      },
      resource_usage: {
        execution_time_sec: Math.random() * 30 + 5,
        cpu_time_sec: Math.random() * 25 + 3,
        gpu_time_sec: Math.random() * 10 + 1,
      },
      custom: {
        proof_complexity: Math.floor(Math.random() * 10) + 1,
        something_else: Math.random() * 100,
        hehe: 'hoho',
        something_array: [1, 2, 3],
        hola: 'hola',
      },
      custom_metrics: {
        proof_complexity: Math.floor(Math.random() * 10) + 1,
        something_else: Math.random() * 100,
        hehe: 'hoho',
        something_array: [1, 2, 3],
        hola: 'hola',
      },
      timestamp: new Date().toISOString(),
    },
    metadata: {
      tags: {
        run_id: 'runId',
        task_id: 'taskId',
      },
    },
  };
};

// Real API functions
const getDataReal: () => Promise<AgentSummary[]> = async () => {
  const response = await axios.get(`${config.DATA_API}/agents`);

  return response.data as AgentSummary[];
};

// Mock API functions
const getDataMock: () => Promise<AgentSummary[]> = async () => {
  await new Promise(resolve => setTimeout(resolve, 500)); // Simulate network delay

  const mockData: AgentSummary[] = [
    {
      agent_name: 'agentA',
      total_runs: 10,
      best_run: {
        run_id: 'run_agentA_001',
        agent_name: 'agentA',
        timestamp_utc: new Date(Date.now() - 2 * 86400000).toISOString(),
        total_tasks: 6,
        success_count: 5,
        failure_count: 1,
        success_rate: 0.83,
        score: 0.9,
        avg_total_tokens: 5000,
        avg_cpu_time_sec: 10.0,
        avg_llm_invocation_count: 7,
        metadata: {
          tags: {
            version: 'A',
            environment: 'test',
          },
        },
      },
    },
    {
      agent_name: 'agentB',
      total_runs: 8,
      best_run: {
        run_id: 'run_agentB_001',
        agent_name: 'agentB',
        timestamp_utc: new Date(Date.now() - 3 * 86400000).toISOString(),
        total_tasks: 6,
        success_count: 4,
        failure_count: 2,
        success_rate: 0.67,
        score: 0.8,
        avg_total_tokens: 4800,
        avg_cpu_time_sec: 12.0,
        avg_llm_invocation_count: 6,
        metadata: {
          tags: {
            version: 'B',
            environment: 'test',
          },
        },
      },
    },
  ];

  return mockData;
};

export const getData = USE_MOCK_DATA ? getDataMock : getDataReal;

const getDetailsReal = async (agentName: string): Promise<AgentRun[]> => {
  const response = await axios.get(
    `${config.DATA_API}/agents/${agentName}/runs`
  );

  return response.data as AgentRun[];
};

const getDetailsMock = async (agentName: string): Promise<AgentRun[]> => {
  await new Promise(resolve => setTimeout(resolve, 300));

  const numRuns = Math.floor(Math.random() * 10) + 5; // 5-15 runs
  const mockRuns: AgentRun[] = [];

  for (let i = 0; i < numRuns; i++) {
    const totalTasks = Math.floor(Math.random() * 50) + 20; // 20-70 tasks
    const successCount = Math.floor(totalTasks * (0.6 + Math.random() * 0.3)); // 60-90% success

    mockRuns.push({
      run_id: `run_${agentName}_${i.toString().padStart(3, '0')}`,
      agent_name: agentName,
      timestamp_utc: new Date(
        Date.now() - Math.random() * 7 * 86400000
      ).toISOString(), // Last 7 days
      total_tasks: totalTasks,
      success_count: successCount,
      failure_count: totalTasks - successCount,
      dataset_id: `dataset_${(Math.floor(Math.random() * 3) + 1).toString().padStart(3, '0')}`,
      metadata: {
        tags: {
          run_id: `run_${agentName}_${i.toString().padStart(3, '0')}`,
          task_id: `task_${agentName}_${i.toString().padStart(3, '0')}`,
          hehe: 'hehe',
          somethingelse: 'somethingelse',
        },
      },
    });
  }

  return mockRuns;
};

export const getDetails = USE_MOCK_DATA ? getDetailsMock : getDetailsReal;

// Get runs for a specific agent within a specific dataset
const getDetailsForDatasetReal = async (
  datasetId: string,
  agentName: string
): Promise<AgentRun[]> => {
  const response = await axios.get(
    `${config.DATA_API}/${datasetId}/agents/${agentName}/runs`
  );

  return response.data as AgentRun[];
};

const getDetailsForDatasetMock = async (
  datasetId: string,
  agentName: string
): Promise<AgentRun[]> => {
  await new Promise(resolve => setTimeout(resolve, 300));

  const numRuns = Math.floor(Math.random() * 10) + 5; // 5-15 runs
  const mockRuns: AgentRun[] = [];

  for (let i = 0; i < numRuns; i++) {
    const totalTasks = Math.floor(Math.random() * 50) + 20; // 20-70 tasks
    const successCount = Math.floor(totalTasks * (0.6 + Math.random() * 0.3)); // 60-90% success

    mockRuns.push({
      run_id: `run_${agentName}_${i.toString().padStart(3, '0')}_${datasetId}`,
      agent_name: agentName,
      timestamp_utc: new Date(
        Date.now() - Math.random() * 7 * 86400000
      ).toISOString(), // Last 7 days
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

export const getDetailsForDataset = USE_MOCK_DATA
  ? getDetailsForDatasetMock
  : getDetailsForDatasetReal;

const getRunDetailsReal = async (
  runIds: string[]
): Promise<RunDetailsResponse[]> => {
  const runIdsParam = runIds.join(',');
  const response = await axios.get(
    `${config.DATA_API}/runs/details?run_ids=${runIdsParam}`
  );
  return response.data as RunDetailsResponse[];
};

const getRunDetailsMock = async (
  runIds: string[]
): Promise<RunDetailsResponse[]> => {
  await new Promise(resolve => setTimeout(resolve, 800));

  // For this mock, always return 2 runs: agentA and agentB
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
    const tasks: TaskOutput[] = [];

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

export const getRunDetails = USE_MOCK_DATA
  ? getRunDetailsMock
  : getRunDetailsReal;

const getObservabilityLogsReal = async (
  runId: string,
  taskId: string
): Promise<Record<string, unknown>> => {
  const encodedTaskId = encodeURIComponent(taskId);
  const response = await axios.get(
    `${config.DATA_API}/observability/logs?run_id=${runId}&task_id=${encodedTaskId}`
  );
  return response.data.labels || {};
};

const getObservabilityLogsMock = async (
  runId: string,
  taskId: string
): Promise<Record<string, unknown>> => {
  await new Promise(resolve => setTimeout(resolve, 400));

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

export const getObservabilityLogs = USE_MOCK_DATA
  ? getObservabilityLogsMock
  : getObservabilityLogsReal;

const refreshDataReal = async (): Promise<{
  success: boolean;
  message: string;
  total_tasks: number;
  total_agents: number;
}> => {
  const response = await axios.post(`${config.DATA_API}/refresh`);
  return response.data;
};

const refreshDataMock = async (): Promise<{
  success: boolean;
  message: string;
  total_tasks: number;
  total_agents: number;
}> => {
  await new Promise(resolve => setTimeout(resolve, 1000));

  const mockRefreshResponse = {
    success: true,
    message: 'Mock data refreshed successfully',
    total_tasks: Math.floor(Math.random() * 1000) + 500,
    total_agents: Math.floor(Math.random() * 10) + 5,
  };

  console.log('Refresh response (MOCK):', mockRefreshResponse);
  return mockRefreshResponse;
};

export const refreshData = USE_MOCK_DATA ? refreshDataMock : refreshDataReal;

export type AgentSummaryTemp = {
  agentName: string;
  totalTasks: number;
  successRate: number;
  avgTime: number;
  avgTokens: number;
  avgLlmCalls: number;
  tags?: Record<string, string>;
};

export async function fetchAgentSummaries(): Promise<AgentSummaryTemp[]> {
  // 1. Fetch all agents

  const agentsRes = await getData();
  const agents: AgentSummary[] = agentsRes;

  // 2. For each agent, fetch their runs
  const summaries = await Promise.all(
    agents.map(async agent => {
      return {
        agentName: agent.agent_name,
        totalTasks: agent.best_run?.total_tasks || 0,
        successRate: agent.best_run
          ? agent.best_run.success_count / agent.best_run.total_tasks
          : 0,
        avgTime: agent.best_run ? agent.best_run.avg_cpu_time_sec : 0,
        avgTokens: agent.best_run ? agent.best_run.avg_total_tokens : 0,
        avgLlmCalls: agent.best_run
          ? agent.best_run.avg_llm_invocation_count
          : 0,
      };
    })
  );

  return summaries;
}

// Benchmark API functions
const getBenchmarksReal = async (): Promise<Benchmark[]> => {
  const response = await axios.get(`${config.DATA_API}/datasets`);
  return response.data as Benchmark[];
};

const getBenchmarksMock = async (): Promise<Benchmark[]> => {
  await new Promise(resolve => setTimeout(resolve, 300));

  const mockBenchmarks: Benchmark[] = [
    {
      dataset_id: 'benchmark_001',
      description: 'Collection of mathematical theorem proving tasks',
      created_at: new Date(Date.now() - 30 * 86400000).toISOString(),
    },
    {
      dataset_id: 'benchmark_002',
      description: 'Logical reasoning and puzzle solving challenges',
      created_at: new Date(Date.now() - 15 * 86400000).toISOString(),
    },
    {
      dataset_id: 'benchmark_003',
      description: 'Logical reasoning and puzzle solving challenges',
      created_at: new Date(Date.now() - 15 * 86400000).toISOString(),
    },
  ];

  console.log('Fetched benchmarks (MOCK):', mockBenchmarks);
  return mockBenchmarks;
};

export const getBenchmarks = USE_MOCK_DATA
  ? getBenchmarksMock
  : getBenchmarksReal;

const getBenchmarkAgentsReal = async (
  benchmarkId: string
): Promise<BenchmarkAgentData> => {
  const response = await axios.get(`${config.DATA_API}/${benchmarkId}/agents`);
  return response.data as BenchmarkAgentData;
};

const getBenchmarkAgentsMock = async (
  benchmarkId: string
): Promise<BenchmarkAgentData> => {
  await new Promise(resolve => setTimeout(resolve, 400));

  const agents = [
    'agentA',
    'agentB',
    'ProofBot-v2.1',
    'CodeGen-Alpha',
    'LogicSolver',
  ];
  const mockAgents: AgentSummary[] = agents.map((agentName, index) => ({
    agent_name: agentName,
    total_runs: Math.floor(Math.random() * 20) + 5,
    best_run: {
      run_id: `run_${agentName}_best_${benchmarkId}`,
      agent_name: agentName,
      timestamp_utc: new Date(
        Date.now() - Math.random() * 7 * 86400000
      ).toISOString(),
      total_tasks: Math.floor(Math.random() * 50) + 20,
      success_count: Math.floor(
        (Math.random() * 0.4 + 0.6) * (Math.floor(Math.random() * 50) + 20)
      ),
      failure_count: Math.floor(
        Math.random() * 0.4 * (Math.floor(Math.random() * 50) + 20)
      ),
      success_rate: Math.random() * 0.4 + 0.6, // 60-100%
      score: Math.random() * 0.4 + 0.6,
      avg_total_tokens: Math.floor(Math.random() * 3000) + 2000,
      avg_cpu_time_sec: Math.random() * 20 + 5,
      avg_llm_invocation_count: Math.floor(Math.random() * 15) + 5,
      metadata: {
        tags: {
          benchmark_id: benchmarkId,
          version: `v${index + 1}.0`,
          environment: 'benchmark',
        },
      },
    },
  }));

  console.log(
    `Fetched agents for benchmark ${benchmarkId} (MOCK):`,
    mockAgents
  );
  return {
    dataset_id: benchmarkId,
    agents: mockAgents,
  };
};

export const getBenchmarkAgents = USE_MOCK_DATA
  ? getBenchmarkAgentsMock
  : getBenchmarkAgentsReal;

// Types for benchmarks

interface BenchmarkAgentData {
  dataset_id: string;
  agents: AgentSummary[];
}
