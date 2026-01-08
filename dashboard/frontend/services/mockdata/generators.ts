import type { TaskOutput } from '@/types/types';

/**
 * Generate a mock task output with static data based on index
 */
export const generateMockTaskOutput = (
  runId: string,
  agentName: string,
  taskIndex: number
): TaskOutput => {
  const isSuccess = taskIndex % 3 !== 2; // Fixed: 70% success rate (0,1,3,4,6,7... succeed, 2,5,8... fail)
  const taskId = taskIndex;
  const taskName = `task_${taskIndex.toString().padStart(3, '0')}`;
  return {
    run_id: runId,
    task_kind: 'FullProofTask',
    task_id: taskId,
    task_name: taskName,
    trace_id: `trace_${taskIndex.toString().padStart(10, '0')}`, // Fixed: deterministic trace ID
    timestamp_utc: new Date(
      Date.now() - taskIndex * 3600000 // Fixed: each task is 1 hour apart
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
      steps_taken: 10 + taskIndex * 2, // Fixed: 10, 12, 14, 16...
    },
    metrics: {
      llm_invocation_count: 8 + taskIndex, // Fixed: 8, 9, 10, 11...
      token_counts: {
        input_tokens: 2000 + taskIndex * 100, // Fixed: 2000, 2100, 2200...
        output_tokens: 800 + taskIndex * 50, // Fixed: 800, 850, 900...
        total_tokens: 2800 + taskIndex * 150, // Fixed: 2800, 2950, 3100...
      },
      resource_usage: {
        execution_time_sec: 12 + taskIndex * 1.5, // Fixed: 12, 13.5, 15...
        cpu_time_sec: 10 + taskIndex * 1.2, // Fixed: 10, 11.2, 12.4...
        gpu_time_sec: 3 + taskIndex * 0.5, // Fixed: 3, 3.5, 4...
      },
      custom: {
        proof_complexity: 5 + (taskIndex % 5), // Fixed: 5, 6, 7, 8, 9, 5...
        something_else: 50 + taskIndex * 5, // Fixed: 50, 55, 60...
        hehe: 'hoho',
        something_array: [1, 2, 3],
        hola: 'hola',
      },
      custom_metrics: {
        proof_complexity: 5 + (taskIndex % 5), // Fixed: 5, 6, 7, 8, 9, 5...
        something_else: 50 + taskIndex * 5, // Fixed: 50, 55, 60...
        hehe: 'hoho',
        something_array: [1, 2, 3],
        hola: 'hola',
      },
      timestamp: new Date().toISOString(),
    },
    metadata: {
      tags: {
        run_id: runId,
        task_id: taskId.toString(),
      },
    },
  };
};

/**
 * Generate a deterministic hex string of specified length based on seed
 */
export const generateHexString = (length: number, seed: number = 0): string => {
  return Array.from({ length }, (_, i) => ((seed + i) % 16).toString(16)).join(
    ''
  );
};

/**
 * Generate a deterministic timestamp within a range
 */
export const generateTimestampInRange = (
  minDaysAgo: number,
  maxDaysAgo: number,
  seed: number = 0
): string => {
  const minMs = minDaysAgo * 86400000;
  const maxMs = maxDaysAgo * 86400000;
  // Use seed to generate deterministic offset
  const ratio = (seed % 100) / 100;
  const randomMs = minMs + ratio * (maxMs - minMs);
  return new Date(Date.now() - randomMs).toISOString();
};

/**
 * Simulate network delay
 */
export const simulateDelay = (minMs: number, maxMs: number): Promise<void> => {
  const delay = minMs + Math.random() * (maxMs - minMs);
  return new Promise(resolve => setTimeout(resolve, delay));
};
