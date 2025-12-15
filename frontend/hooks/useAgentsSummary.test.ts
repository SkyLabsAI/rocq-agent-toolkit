import { renderHook, waitFor } from '@testing-library/react';

import {
  fetchAgentSummaries,
  getData,
  getObservabilityLogs,
} from '@/services/dataservice';
import { type TaskOutput } from '@/types/types';

import { useAgents } from './useAgentsSummary';

jest.mock('@/services/dataservice');

const mockGetData = getData as jest.MockedFunction<typeof getData>;
const mockFetchAgentSummaries = fetchAgentSummaries as jest.MockedFunction<
  typeof fetchAgentSummaries
>;
const mockGetObservabilityLogs = getObservabilityLogs as jest.MockedFunction<
  typeof getObservabilityLogs
>;

describe('useAgents', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('should fetch data on mount', async () => {
    const mockAgents = [
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
    ];

    const mockSummaries = [
      {
        agentName: 'agent1',
        totalTasks: 10,
        successRate: 0.8,
        avgTime: 5.5,
        avgTokens: 1000,
        avgLlmCalls: 3,
      },
    ];

    mockGetData.mockResolvedValue(mockAgents);
    mockFetchAgentSummaries.mockResolvedValue(mockSummaries);

    const { result } = renderHook(() => useAgents());

    expect(result.current.isLoading).toBe(true);

    await waitFor(() => {
      expect(result.current.isLoading).toBe(false);
    });

    expect(result.current.agentData).toEqual(mockAgents);
    expect(result.current.agentDetailData).toEqual(mockSummaries);
  });

  it('should open code modal and fetch logs', async () => {
    mockGetData.mockResolvedValue([]);
    mockFetchAgentSummaries.mockResolvedValue([]);

    const mockLogs = { log1: 'test log' };
    mockGetObservabilityLogs.mockResolvedValue(mockLogs);

    const { result } = renderHook(() => useAgents());

    await waitFor(() => {
      expect(result.current.isLoading).toBe(false);
    });

    const mockTask: TaskOutput = {
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
    };

    await result.current.openCodeModal(mockTask);

    await waitFor(() => {
      expect(result.current.modalState.isOpen).toBe(true);
      expect(result.current.modalState.selectedTask).toEqual(mockTask);
      expect(result.current.modalState.logs).toEqual(mockLogs);
    });
  });

  it('should handle error when opening code modal', async () => {
    const consoleError = jest.spyOn(console, 'error').mockImplementation();
    mockGetData.mockResolvedValue([]);
    mockFetchAgentSummaries.mockResolvedValue([]);
    mockGetObservabilityLogs.mockRejectedValue(new Error('Fetch error'));

    const { result } = renderHook(() => useAgents());

    await waitFor(() => {
      expect(result.current.isLoading).toBe(false);
    });

    const mockTask: TaskOutput = {
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
    };

    await result.current.openCodeModal(mockTask);

    await waitFor(() => {
      expect(result.current.modalState.logs).toEqual({
        error: 'Failed to load logs',
      });
    });

    consoleError.mockRestore();
  });

  it('should close modal', async () => {
    mockGetData.mockResolvedValue([]);
    mockFetchAgentSummaries.mockResolvedValue([]);

    const { result } = renderHook(() => useAgents());

    await waitFor(() => {
      expect(result.current.isLoading).toBe(false);
    });

    const mockTask: TaskOutput = {
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
    };

    mockGetObservabilityLogs.mockResolvedValue({});
    await result.current.openCodeModal(mockTask);

    await waitFor(() => {
      expect(result.current.modalState.isOpen).toBe(true);
    });

    result.current.closeModal();

    expect(result.current.modalState.isOpen).toBe(false);
    expect(result.current.modalState.selectedTask).toBe(null);
    expect(result.current.modalState.logs).toBe(null);
  });
});
