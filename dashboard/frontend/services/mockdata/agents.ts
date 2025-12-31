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

  const numInstances = Math.floor(Math.random() * 3) + 2; // 2-4 instances
  const mockInstances: AgentInstanceSummary[] = [];

  for (let i = 0; i < numInstances; i++) {
    const totalTasks = Math.floor(Math.random() * 50) + 20;
    const successCount = Math.floor(totalTasks * (0.6 + Math.random() * 0.3));

    mockInstances.push({
      agent_checksum: `instance-${agentClsChecksum}-${i}`,
      cls_checksum: agentClsChecksum,
      name: `Instance ${i + 1}`,
      provenance: {
        version: `v${i + 1}.0`,
        created_at: new Date(
          Date.now() - Math.random() * 30 * 86400000
        ).toISOString(),
      },
      total_runs: Math.floor(Math.random() * 10) + 3,
      best_run: {
        run_id: `run_instance_${i}_001`,
        agent_cls_checksum: agentClsChecksum,
        agent_checksum: `instance-${agentClsChecksum}-${i}`,
        timestamp_utc: new Date(
          Date.now() - Math.random() * 7 * 86400000
        ).toISOString(),
        total_tasks: totalTasks,
        success_count: successCount,
        failure_count: totalTasks - successCount,
        success_rate: successCount / totalTasks,
        score: 0.8 + Math.random() * 0.2,
        avg_total_tokens: 4000 + Math.random() * 2000,
        avg_cpu_time_sec: 8 + Math.random() * 8,
        avg_llm_invocation_count: 5 + Math.random() * 5,
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

  const numInstances = Math.floor(Math.random() * 3) + 2;
  const mockInstances: AgentInstanceSummary[] = [];

  for (let i = 0; i < numInstances; i++) {
    const totalTasks = Math.floor(Math.random() * 50) + 20;
    const successCount = Math.floor(totalTasks * (0.6 + Math.random() * 0.3));

    mockInstances.push({
      agent_checksum: `dataset-${datasetId}-instance-${agentClsChecksum}-${i}`,
      cls_checksum: agentClsChecksum,
      name: `Instance ${i + 1}`,
      provenance: {
        version: `v${i + 1}.0`,
        dataset: datasetId,
        created_at: new Date(
          Date.now() - Math.random() * 30 * 86400000
        ).toISOString(),
      },
      total_runs: Math.floor(Math.random() * 10) + 3,
      best_run: {
        run_id: `run_dataset_${datasetId}_instance_${i}_001`,
        agent_cls_checksum: agentClsChecksum,
        agent_checksum: `dataset-${datasetId}-instance-${agentClsChecksum}-${i}`,
        timestamp_utc: new Date(
          Date.now() - Math.random() * 7 * 86400000
        ).toISOString(),
        dataset_id: datasetId,
        total_tasks: totalTasks,
        success_count: successCount,
        failure_count: totalTasks - successCount,
        success_rate: successCount / totalTasks,
        score: 0.8 + Math.random() * 0.2,
        avg_total_tokens: 4000 + Math.random() * 2000,
        avg_cpu_time_sec: 8 + Math.random() * 8,
        avg_llm_invocation_count: 5 + Math.random() * 5,
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

  const numRuns = Math.floor(Math.random() * 10) + 5; // 5-15 runs
  const mockRuns: AgentRun[] = [];

  for (let i = 0; i < numRuns; i++) {
    const totalTasks = Math.floor(Math.random() * 50) + 20;
    const successCount = Math.floor(totalTasks * (0.6 + Math.random() * 0.3));

    mockRuns.push({
      run_id: `run_${agentName}_${i.toString().padStart(3, '0')}`,
      agent_name: agentName,
      timestamp_utc: new Date(
        Date.now() - Math.random() * 7 * 86400000
      ).toISOString(),
      total_tasks: totalTasks,
      success_count: successCount,
      failure_count: totalTasks - successCount,
      dataset_id: `benchmark_${(Math.floor(Math.random() * 3) + 1).toString().padStart(3, '0')}`,
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
