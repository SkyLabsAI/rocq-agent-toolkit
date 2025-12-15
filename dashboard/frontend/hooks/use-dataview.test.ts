import { renderHook, waitFor } from '@testing-library/react';

import { getBenchmarkAgents, getBenchmarks } from '@/services/dataservice';

import { useBenchmarks } from './use-dataview';

jest.mock('@/services/dataservice');

const mockGetBenchmarks = getBenchmarks as jest.MockedFunction<
  typeof getBenchmarks
>;
const mockGetBenchmarkAgents = getBenchmarkAgents as jest.MockedFunction<
  typeof getBenchmarkAgents
>;

describe('useBenchmarks', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('should fetch benchmarks on mount', async () => {
    const mockBenchmarks = [
      {
        dataset_id: 'bench1',
        description: 'Test Benchmark',
        created_at: '2024-01-01',
      },
    ];
    mockGetBenchmarks.mockResolvedValue(mockBenchmarks);

    const { result } = renderHook(() => useBenchmarks());

    await waitFor(() => {
      expect(result.current.loading).toBe(false);
    });

    expect(mockGetBenchmarks).toHaveBeenCalled();
    expect(result.current.benchmarks).toEqual(mockBenchmarks);
  });

  it('should handle benchmark fetch error', async () => {
    const consoleError = jest.spyOn(console, 'error').mockImplementation();
    mockGetBenchmarks.mockRejectedValue(new Error('Network error'));

    const { result } = renderHook(() => useBenchmarks());

    await waitFor(() => {
      expect(result.current.loading).toBe(false);
    });

    expect(consoleError).toHaveBeenCalled();
    consoleError.mockRestore();
  });

  it('should fetch agents for a specific benchmark', async () => {
    const mockBenchmarks = [
      { dataset_id: 'bench1', description: 'Test', created_at: '2024-01-01' },
    ];
    const mockAgentData = {
      dataset_id: 'bench1',
      agents: [
        {
          agent_name: 'agent1',
          total_runs: 5,
          best_run: {
            run_id: 'run1',
            agent_name: 'agent1',
            timestamp_utc: '2024-01-01',
            total_tasks: 10,
            success_count: 8,
            failure_count: 2,
            success_rate: 0.8,
            score: 0.85,
            avg_total_tokens: 1000,
            avg_cpu_time_sec: 5.5,
            avg_llm_invocation_count: 3,
            metadata: { tags: {} },
          },
        },
      ],
    };

    mockGetBenchmarks.mockResolvedValue(mockBenchmarks);
    mockGetBenchmarkAgents.mockResolvedValue(mockAgentData);

    const { result } = renderHook(() => useBenchmarks());

    await waitFor(() => {
      expect(result.current.loading).toBe(false);
    });

    await result.current.fetchAgentsForBenchmark('bench1');

    await waitFor(() => {
      expect(result.current.benchmarkAgents.get('bench1')).toEqual(
        mockAgentData.agents
      );
    });
  });

  it('should handle error when fetching agents for benchmark', async () => {
    const consoleError = jest.spyOn(console, 'error').mockImplementation();
    mockGetBenchmarks.mockResolvedValue([]);
    mockGetBenchmarkAgents.mockRejectedValue(new Error('Fetch error'));

    const { result } = renderHook(() => useBenchmarks());

    await waitFor(() => {
      expect(result.current.loading).toBe(false);
    });

    await result.current.fetchAgentsForBenchmark('bench1');

    expect(consoleError).toHaveBeenCalled();
    consoleError.mockRestore();
  });
});
