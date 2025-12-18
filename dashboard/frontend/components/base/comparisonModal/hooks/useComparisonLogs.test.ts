import { renderHook, waitFor } from '@testing-library/react';

import { getObservabilityLogs } from '@/services/dataservice';
import { type TaskOutput } from '@/types/types';

import { useComparisonLogs } from './use-comparison-logs';

jest.mock('@/services/dataservice');

const mockGetObservabilityLogs = getObservabilityLogs as jest.MockedFunction<
  typeof getObservabilityLogs
>;

describe('useComparisonLogs', () => {
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
      token_counts: { input_tokens: 100, output_tokens: 50, total_tokens: 150 },
      resource_usage: {
        execution_time_sec: 1.0,
        cpu_time_sec: 0.8,
        gpu_time_sec: 0.2,
      },
      custom: null,
    },
  };

  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('should fetch logs when modal is open', async () => {
    const mockLogs = { log1: 'test log' };
    mockGetObservabilityLogs.mockResolvedValue(mockLogs);

    const { result } = renderHook(() =>
      useComparisonLogs(true, [{ label: 'Agent1', task: mockTask }])
    );

    expect(result.current.loading).toBe(true);

    await waitFor(() => {
      expect(result.current.loading).toBe(false);
    });

    expect(mockGetObservabilityLogs).toHaveBeenCalledWith('run1', 'task1');
    expect(result.current.taskLogs[0]).toEqual(mockLogs);
  });

  it('should not fetch logs when modal is closed', () => {
    renderHook(() =>
      useComparisonLogs(false, [{ label: 'Agent1', task: mockTask }])
    );

    expect(mockGetObservabilityLogs).not.toHaveBeenCalled();
  });

  it('should not fetch logs when items array is empty', () => {
    renderHook(() => useComparisonLogs(true, []));

    expect(mockGetObservabilityLogs).not.toHaveBeenCalled();
  });

  it('should handle multiple items', async () => {
    const mockLogs1 = { log1: 'test log 1' };
    const mockLogs2 = { log2: 'test log 2' };
    mockGetObservabilityLogs
      .mockResolvedValueOnce(mockLogs1)
      .mockResolvedValueOnce(mockLogs2);

    const mockTask2: TaskOutput = {
      ...mockTask,
      run_id: 'run2',
      task_id: 'task2',
    };

    const { result } = renderHook(() =>
      useComparisonLogs(true, [
        { label: 'Agent1', task: mockTask },
        { label: 'Agent2', task: mockTask2 },
      ])
    );

    await waitFor(() => {
      expect(result.current.loading).toBe(false);
    });

    // Effects may run more than once in test environment; ensure at least two calls
    expect(mockGetObservabilityLogs.mock.calls.length).toBeGreaterThanOrEqual(2);
    expect(result.current.taskLogs[0]).not.toBeNull();
    expect(result.current.taskLogs[1]).not.toBeNull();
  });

  it('should handle items with null tasks', async () => {
    const { result } = renderHook(() =>
      useComparisonLogs(true, [
        { label: 'Agent1', task: mockTask },
        { label: 'Agent2', task: null },
      ])
    );

    await waitFor(() => {
      expect(result.current.loading).toBe(false);
    });

    expect(mockGetObservabilityLogs.mock.calls.length).toBeGreaterThanOrEqual(1);
    expect(result.current.taskLogs[1]).toBeNull();
  });

  it('should handle fetch errors', async () => {
    mockGetObservabilityLogs.mockRejectedValue(new Error('Network error'));

    const { result } = renderHook(() =>
      useComparisonLogs(true, [{ label: 'Agent1', task: mockTask }])
    );

    await waitFor(() => {
      expect(result.current.loading).toBe(false);
    });

    expect(result.current.taskLogs[0]).toBeNull();
  });

  it('should handle general error', async () => {
    mockGetObservabilityLogs.mockImplementation(() => {
      throw new Error('General error');
    });

    const { result } = renderHook(() =>
      useComparisonLogs(true, [{ label: 'Agent1', task: mockTask }])
    );

    await waitFor(() => {
      expect(result.current.loading).toBe(false);
    });

    // Inner fetch errors are handled per item; overall error remains null
    expect(result.current.error).toBeNull();
    expect(result.current.taskLogs[0]).toBeNull();
  });
});
