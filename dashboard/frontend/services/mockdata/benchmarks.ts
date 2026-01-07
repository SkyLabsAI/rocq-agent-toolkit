import type { AgentSummary, Benchmark } from '@/types/types';

import { simulateDelay } from './generators';

/**
 * Mock data for benchmarks/datasets list
 */
export const getBenchmarksMock = async (): Promise<Benchmark[]> => {
  await simulateDelay(200, 500);

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
      description: 'Advanced formal verification test suite',
      created_at: new Date(Date.now() - 7 * 86400000).toISOString(),
    },
  ];

  console.log('Fetched benchmarks (MOCK):', mockBenchmarks);
  return mockBenchmarks;
};

/**
 * Mock data for agents within a specific benchmark
 */
export const getBenchmarkAgentsMock = async (
  benchmarkId: string
): Promise<AgentSummary[]> => {
  await simulateDelay(300, 600);

  const agents = [
    'agentA',
    'agentB',
    'ProofBot-v2.1',
    'CodeGen-Alpha',
    'LogicSolver',
  ];

  const mockAgents: AgentSummary[] = agents.map((agentName, index) => ({
    cls_name: agentName,
    cls_checksum: `checksum-${index + 1}`,
    cls_provenance: {},
    total_runs: Math.floor(Math.random() * 20) + 5,
    best_run: {
      run_id: `run_${agentName}_best_${benchmarkId}`,
      agent_cls_checksum: `checksum-${index + 1}`,
      agent_checksum: `checksum-${index + 1}`,
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
  return mockAgents;
};
