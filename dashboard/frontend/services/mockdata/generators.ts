import type { TaskOutput } from '@/types/types';

/**
 * Generate a random mock task output with realistic data
 */
export const generateMockTaskOutput = (
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
        run_id: runId,
        task_id: taskId,
      },
    },
  };
};

/**
 * Generate a random hex string of specified length
 */
export const generateHexString = (length: number): string => {
  return Array.from({ length }, () =>
    Math.floor(Math.random() * 16).toString(16)
  ).join('');
};

/**
 * Generate a random timestamp within a range
 */
export const generateTimestampInRange = (
  minDaysAgo: number,
  maxDaysAgo: number
): string => {
  const minMs = minDaysAgo * 86400000;
  const maxMs = maxDaysAgo * 86400000;
  const randomMs = minMs + Math.random() * (maxMs - minMs);
  return new Date(Date.now() - randomMs).toISOString();
};

/**
 * Simulate network delay
 */
export const simulateDelay = (minMs: number, maxMs: number): Promise<void> => {
  const delay = minMs + Math.random() * (maxMs - minMs);
  return new Promise(resolve => setTimeout(resolve, delay));
};
