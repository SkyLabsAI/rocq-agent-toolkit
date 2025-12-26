import { type RunDetailsResponse, type TaskOutput } from '@/types/types';

import { computeRunStats, transformRunsToTaskRows } from './utils';

describe('utils', () => {
  describe('computeRunStats', () => {
    it('should compute stats for a run with tasks', () => {
      const run: RunDetailsResponse = {
        run_id: 'run1',
        agent_name: 'agent1',
        total_tasks: 3,
        tasks: [
          {
            run_id: 'run1',
            task_kind: 'FullProofTask',
            task_id: 'task1',
            timestamp_utc: '2024-01-01',
            agent_name: 'agent1',
            status: 'Success',
            results: {},
            metrics: {
              llm_invocation_count: 5,
              token_counts: {
                input_tokens: 100,
                output_tokens: 50,
                total_tokens: 150,
              },
              resource_usage: {
                execution_time_sec: 2.0,
                cpu_time_sec: 1.5,
                gpu_time_sec: 0.5,
              },
              custom: null,
            },
          },
          {
            run_id: 'run1',
            task_kind: 'FullProofTask',
            task_id: 'task2',
            timestamp_utc: '2024-01-01',
            agent_name: 'agent1',
            status: 'Success',
            results: {},
            metrics: {
              llm_invocation_count: 3,
              token_counts: {
                input_tokens: 80,
                output_tokens: 40,
                total_tokens: 120,
              },
              resource_usage: {
                execution_time_sec: 1.5,
                cpu_time_sec: 1.0,
                gpu_time_sec: 0.5,
              },
              custom: null,
            },
          },
          {
            run_id: 'run1',
            task_kind: 'FullProofTask',
            task_id: 'task3',
            timestamp_utc: '2024-01-01',
            agent_name: 'agent1',
            status: 'Failure',
            results: {},
            metrics: {
              llm_invocation_count: 2,
              token_counts: {
                input_tokens: 60,
                output_tokens: 30,
                total_tokens: 90,
              },
              resource_usage: {
                execution_time_sec: 1.0,
                cpu_time_sec: 0.8,
                gpu_time_sec: 0.2,
              },
              custom: null,
            },
          },
        ],
      };

      const stats = computeRunStats(run);

      expect(stats.id).toBe('run1');
      expect(stats.name).toBe('agent1');
      expect(stats.tasks).toBe(3);
      expect(stats.successRate).toBeCloseTo(2 / 3, 2);
      expect(stats.totalLlmCalls).toBe(10);
      expect(stats.totalTokens).toBe(360);
      expect(stats.avgExecutionTime).toBeCloseTo(1.5, 2);
    });

    it('should handle empty tasks array', () => {
      const run: RunDetailsResponse = {
        run_id: 'run1',
        agent_name: 'agent1',
        total_tasks: 0,
        tasks: [],
      };

      const stats = computeRunStats(run);

      expect(stats.tasks).toBe(0);
      expect(stats.successRate).toBe(0);
      expect(stats.totalLlmCalls).toBe(0);
      expect(stats.totalTokens).toBe(0);
      expect(stats.avgExecutionTime).toBe(0);
    });

    it('should handle tasks with missing metrics', () => {
      const run: RunDetailsResponse = {
        run_id: 'run1',
        agent_name: 'agent1',
        total_tasks: 1,
        tasks: [
          {
            run_id: 'run1',
            task_kind: 'FullProofTask',
            task_id: 'task1',
            timestamp_utc: '2024-01-01',
            agent_name: 'agent1',
            status: 'Success',
            results: {},
            metrics: {
              llm_invocation_count: 0,
              token_counts: {
                input_tokens: 0,
                output_tokens: 0,
                total_tokens: 0,
              },
              resource_usage: {
                execution_time_sec: 0,
                cpu_time_sec: 0,
                gpu_time_sec: 0,
              },
              custom: null,
            },
          },
        ],
      };

      const stats = computeRunStats(run);

      expect(stats.totalLlmCalls).toBe(0);
      expect(stats.totalTokens).toBe(0);
      expect(stats.avgExecutionTime).toBe(0);
    });
  });

  describe('transformRunsToTaskRows', () => {
    it('should transform runs to task rows correctly', () => {
      const runs: RunDetailsResponse[] = [
        {
          run_id: 'run1',
          agent_name: 'agent1',
          total_tasks: 2,
          tasks: [
            {
              run_id: 'run1',
              task_kind: 'FullProofTask',
              task_id: 'task1',
              timestamp_utc: '2024-01-01',
              agent_name: 'agent1',
              status: 'Success',
              results: {},
              metrics: {
                llm_invocation_count: 1,
                token_counts: {
                  input_tokens: 100,
                  output_tokens: 50,
                  total_tokens: 150,
                },
                resource_usage: {
                  execution_time_sec: 1.0,
                  cpu_time_sec: 0.8,
                  gpu_time_sec: 0.2,
                },
                custom: null,
              },
            },
            {
              run_id: 'run1',
              task_kind: 'FullProofTask',
              task_id: 'task2',
              timestamp_utc: '2024-01-01',
              agent_name: 'agent1',
              status: 'Success',
              results: {},
              metrics: {
                llm_invocation_count: 1,
                token_counts: {
                  input_tokens: 100,
                  output_tokens: 50,
                  total_tokens: 150,
                },
                resource_usage: {
                  execution_time_sec: 1.0,
                  cpu_time_sec: 0.8,
                  gpu_time_sec: 0.2,
                },
                custom: null,
              },
            },
          ],
        },
        {
          run_id: 'run2',
          agent_name: 'agent2',
          total_tasks: 2,
          tasks: [
            {
              run_id: 'run2',
              task_kind: 'FullProofTask',
              task_id: 'task1',
              timestamp_utc: '2024-01-01',
              agent_name: 'agent2',
              status: 'Failure',
              results: {},
              metrics: {
                llm_invocation_count: 1,
                token_counts: {
                  input_tokens: 100,
                  output_tokens: 50,
                  total_tokens: 150,
                },
                resource_usage: {
                  execution_time_sec: 1.0,
                  cpu_time_sec: 0.8,
                  gpu_time_sec: 0.2,
                },
                custom: null,
              },
            },
            {
              run_id: 'run2',
              task_kind: 'FullProofTask',
              task_id: 'task3',
              timestamp_utc: '2024-01-01',
              agent_name: 'agent2',
              status: 'Success',
              results: {},
              metrics: {
                llm_invocation_count: 1,
                token_counts: {
                  input_tokens: 100,
                  output_tokens: 50,
                  total_tokens: 150,
                },
                resource_usage: {
                  execution_time_sec: 1.0,
                  cpu_time_sec: 0.8,
                  gpu_time_sec: 0.2,
                },
                custom: null,
              },
            },
          ],
        },
      ];

      const result = transformRunsToTaskRows(runs);

      expect(result).toHaveLength(3); // task1, task2, task3
      expect(result[0].taskId).toBe('task1');
      expect(result[0].cells).toHaveLength(2);
      expect(result[0].cells[0]).toBeTruthy();
      expect(result[0].cells[0]?.runId).toBe('run1');
      expect(result[0].cells[1]).toBeTruthy();
      expect(result[0].cells[1]?.runId).toBe('run2');
    });

    it('should handle empty runs array', () => {
      const result = transformRunsToTaskRows([]);
      expect(result).toEqual([]);
    });

    it('should sort task rows by task ID', () => {
      const runs: RunDetailsResponse[] = [
        {
          run_id: 'run1',
          agent_name: 'agent1',
          total_tasks: 2,
          tasks: [
            {
              run_id: 'run1',
              task_kind: 'FullProofTask',
              task_id: 'task_z',
              timestamp_utc: '2024-01-01',
              agent_name: 'agent1',
              status: 'Success',
              results: {},
              metrics: {
                llm_invocation_count: 1,
                token_counts: {
                  input_tokens: 100,
                  output_tokens: 50,
                  total_tokens: 150,
                },
                resource_usage: {
                  execution_time_sec: 1.0,
                  cpu_time_sec: 0.8,
                  gpu_time_sec: 0.2,
                },
                custom: null,
              },
            },
            {
              run_id: 'run1',
              task_kind: 'FullProofTask',
              task_id: 'task_a',
              timestamp_utc: '2024-01-01',
              agent_name: 'agent1',
              status: 'Success',
              results: {},
              metrics: {
                llm_invocation_count: 1,
                token_counts: {
                  input_tokens: 100,
                  output_tokens: 50,
                  total_tokens: 150,
                },
                resource_usage: {
                  execution_time_sec: 1.0,
                  cpu_time_sec: 0.8,
                  gpu_time_sec: 0.2,
                },
                custom: null,
              },
            },
          ],
        },
      ];

      const result = transformRunsToTaskRows(runs);
      expect(result[0].taskId).toBe('task_a');
      expect(result[1].taskId).toBe('task_z');
    });
  });
});
