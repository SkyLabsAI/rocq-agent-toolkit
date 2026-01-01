import type {
  AgentInstanceSummary,
  AgentRun,
  AgentSummary,
} from '@/types/types';

import { simulateDelay } from './generators';

/**
 * Mock data for agent class summaries
 */
export const getAgentClassDataMock = async (): Promise<AgentSummary[]> => {
  await simulateDelay(300, 700);

  const mockData: AgentSummary[] = [
    {
      cls_name: 'agentA',
      cls_checksum: 'checksum-1',
      cls_provenance: {},
      total_runs: 10,
      best_run: {
        run_id: 'run_agentA_001',
        agent_cls_checksum: 'checksum-1',
        agent_checksum: 'checksum-1',
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
      cls_name: 'agentB',
      cls_checksum: 'checksum-2',
      cls_provenance: {},
      total_runs: 8,
      best_run: {
        run_id: 'run_agentB_001',
        agent_cls_checksum: 'checksum-2',
        agent_checksum: 'checksum-2',
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
    {
      cls_name: 'ProofBot-v2.1',
      cls_checksum: 'checksum-3',
      cls_provenance: {},
      total_runs: 15,
      best_run: {
        run_id: 'run_proofbot_001',
        agent_cls_checksum: 'checksum-3',
        agent_checksum: 'checksum-3',
        timestamp_utc: new Date(Date.now() - 1 * 86400000).toISOString(),
        total_tasks: 8,
        success_count: 7,
        failure_count: 1,
        success_rate: 0.875,
        score: 0.95,
        avg_total_tokens: 6200,
        avg_cpu_time_sec: 8.5,
        avg_llm_invocation_count: 9,
        metadata: {
          tags: {
            version: 'v2.1',
            environment: 'production',
          },
        },
      },
    },
  ];

  return mockData;
};

/**
 * Mock data for agent instances within a class
 */
export const getAgentInstancesMock = async (
  agentClsChecksum: string
): Promise<AgentInstanceSummary[]> => {
  await simulateDelay(200, 500);

  const numInstances = 3; // Fixed: always return 3 instances
  const mockInstances: AgentInstanceSummary[] = [];

  for (let i = 0; i < numInstances; i++) {
    const totalTasks = 30 + i * 10; // Fixed: 30, 40, 50
    const successCount = Math.floor(totalTasks * 0.75); // Fixed: 75% success rate

    mockInstances.push({
      agent_checksum: `instance-${agentClsChecksum}-${i}`,
      cls_checksum: agentClsChecksum,
      name: `Instance ${i + 1}`,
      provenance: {
        version: `v${i + 1}.0`,
        created_at: new Date(
          Date.now() - (i + 1) * 7 * 86400000 // Fixed: 7, 14, 21 days ago
        ).toISOString(),
      },
      total_runs: 5 + i, // Fixed: 5, 6, 7 runs
      best_run: {
        run_id: `run_instance_${i}_001`,
        agent_cls_checksum: agentClsChecksum,
        agent_checksum: `instance-${agentClsChecksum}-${i}`,
        timestamp_utc: new Date(
          Date.now() - (i + 1) * 2 * 86400000 // Fixed: 2, 4, 6 days ago
        ).toISOString(),
        total_tasks: totalTasks,
        success_count: successCount,
        failure_count: totalTasks - successCount,
        success_rate: successCount / totalTasks,
        score: 0.85 + i * 0.05, // Fixed: 0.85, 0.90, 0.95
        avg_total_tokens: 4500 + i * 500, // Fixed: 4500, 5000, 5500
        avg_cpu_time_sec: 10 + i * 2, // Fixed: 10, 12, 14
        avg_llm_invocation_count: 6 + i, // Fixed: 6, 7, 8
        best_run: false,
        metadata: {
          tags: {},
        },
      },
    });
  }

  return mockInstances;
};

/**
 * Mock data for dataset-specific agent instances
 */
export const getDatasetAgentInstancesMock = async (
  datasetId: string,
  agentClsChecksum: string
): Promise<AgentInstanceSummary[]> => {
  await simulateDelay(200, 500);

  const numInstances = 3; // Fixed: always return 3 instances
  const mockInstances: AgentInstanceSummary[] = [];

  for (let i = 0; i < numInstances; i++) {
    const totalTasks = 35 + i * 10; // Fixed: 35, 45, 55
    const successCount = Math.floor(totalTasks * 0.8); // Fixed: 80% success rate

    mockInstances.push({
      agent_checksum: `dataset-${datasetId}-instance-${agentClsChecksum}-${i}`,
      cls_checksum: agentClsChecksum,
      name: `Instance ${i + 1}`,
      provenance: {
        version: `v${i + 1}.0`,
        dataset: datasetId,
        created_at: new Date(
          Date.now() - (i + 1) * 10 * 86400000 // Fixed: 10, 20, 30 days ago
        ).toISOString(),
      },
      total_runs: 4 + i, // Fixed: 4, 5, 6 runs
      best_run: {
        run_id: `run_dataset_${datasetId}_instance_${i}_001`,
        agent_cls_checksum: agentClsChecksum,
        agent_checksum: `dataset-${datasetId}-instance-${agentClsChecksum}-${i}`,
        timestamp_utc: new Date(
          Date.now() - (i + 1) * 3 * 86400000 // Fixed: 3, 6, 9 days ago
        ).toISOString(),
        dataset_id: datasetId,
        total_tasks: totalTasks,
        success_count: successCount,
        failure_count: totalTasks - successCount,
        success_rate: successCount / totalTasks,
        score: 0.82 + i * 0.06, // Fixed: 0.82, 0.88, 0.94
        avg_total_tokens: 4200 + i * 600, // Fixed: 4200, 4800, 5400
        avg_cpu_time_sec: 9 + i * 2, // Fixed: 9, 11, 13
        avg_llm_invocation_count: 7 + i, // Fixed: 7, 8, 9
        best_run: false,
        metadata: {
          tags: {
            dataset: datasetId,
          },
        },
      },
    });
  }

  return mockInstances;
};

/**
 * Mock data for agent runs by class name
 */
export const getDetailsMock = async (
  agentName: string
): Promise<AgentRun[]> => {
  await simulateDelay(200, 500);

  const numRuns = 8; // Fixed: always return 8 runs
  const mockRuns: AgentRun[] = [];

  for (let i = 0; i < numRuns; i++) {
    const totalTasks = 25 + i * 5; // Fixed: 25, 30, 35, 40, 45, 50, 55, 60
    const successCount = Math.floor(totalTasks * 0.7); // Fixed: 70% success rate

    mockRuns.push({
      run_id: `run_${agentName}_${i.toString().padStart(3, '0')}`,
      agent_name: agentName,
      timestamp_utc: new Date(
        Date.now() - (i + 1) * 1 * 86400000 // Fixed: 1, 2, 3... days ago
      ).toISOString(),
      total_tasks: totalTasks,
      success_count: successCount,
      failure_count: totalTasks - successCount,
      dataset_id: `benchmark_${((i % 3) + 1).toString().padStart(3, '0')}`, // Fixed: cycles through benchmark_001, 002, 003
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

  console.log(
    `Fetched ${mockRuns.length} runs for agent ${agentName} (MOCK)`,
    mockRuns
  );
  return mockRuns;
};
