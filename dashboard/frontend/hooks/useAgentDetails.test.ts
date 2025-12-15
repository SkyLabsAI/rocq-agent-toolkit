import { act, renderHook, waitFor } from '@testing-library/react';

import { getDetails, getRunDetails } from '@/services/dataservice';
import { type AgentRun, type TaskOutput } from '@/types/types';

import { useAgentDetails } from './useAgentDetails';

// Mock the dataservice
jest.mock('@/services/dataservice', () => ({
  getDetails: jest.fn(),
  getRunDetails: jest.fn(),
}));

const mockGetDetails = getDetails as jest.MockedFunction<typeof getDetails>;
const mockGetRunDetails = getRunDetails as jest.MockedFunction<
  typeof getRunDetails
>;

describe('useAgentDetails', () => {
  const mockAgentName = 'test-agent';

  const mockRunDetails: AgentRun[] = [
    {
      run_id: 'run-1',
      agent_name: 'test-agent',
      timestamp_utc: '2024-01-01T00:00:00Z',
      total_tasks: 10,
      success_count: 8,
      failure_count: 2,
      dataset_id: 'dataset-1',
      metadata: { tags: {} },
    },
    {
      run_id: 'run-2',
      agent_name: 'test-agent',
      timestamp_utc: '2024-01-02T00:00:00Z',
      total_tasks: 15,
      success_count: 12,
      failure_count: 3,
      dataset_id: 'dataset-1',
      metadata: { tags: {} },
    },
  ];

  const mockTaskOutputs: TaskOutput[] = [
    {
      run_id: 'run-1',
      task_kind: 'FullProofTask',
      task_id: 'task-1',
      timestamp_utc: '2024-01-01T00:00:00Z',
      agent_name: 'test-agent',
      status: 'Success',
      results: null,
      metrics: {
        llm_invocation_count: 5,
        token_counts: {
          input_tokens: 100,
          output_tokens: 50,
          total_tokens: 150,
        },
        resource_usage: {
          execution_time_sec: 1.5,
          cpu_time_sec: 1.0,
          gpu_time_sec: 0.5,
        },
        custom: null,
      },
    },
  ];

  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('should initialize with default values', () => {
    const { result } = renderHook(() => useAgentDetails(mockAgentName));

    expect(result.current.loading).toBe(false);
    expect(result.current.isOpen).toBe(false);
    expect(result.current.taskDetails).toEqual([]);
    expect(result.current.runDetails).toEqual([]);
    expect(result.current.runTaskDetails.size).toBe(0);
    expect(result.current.loadingRunDetails.size).toBe(0);
  });

  it('should fetch agent details on openDetails', async () => {
    mockGetDetails.mockResolvedValue(mockRunDetails);

    const { result } = renderHook(() => useAgentDetails(mockAgentName));

    await act(async () => {
      await result.current.openDetails();
    });

    expect(mockGetDetails).toHaveBeenCalledWith(mockAgentName);
    expect(result.current.runDetails).toEqual(mockRunDetails);
    expect(result.current.loading).toBe(false);
  });

  it('should toggle details open and closed', async () => {
    mockGetDetails.mockResolvedValue(mockRunDetails);

    const { result } = renderHook(() => useAgentDetails(mockAgentName));

    expect(result.current.isOpen).toBe(false);

    // Open details
    await act(async () => {
      await result.current.toggleDetails();
    });

    expect(result.current.isOpen).toBe(true);
    expect(mockGetDetails).toHaveBeenCalledWith(mockAgentName);

    // Close details
    await act(async () => {
      result.current.toggleDetails();
    });

    expect(result.current.isOpen).toBe(false);
  });

  it('should fetch run details for given run IDs', async () => {
    const mockRunDetailsResponse = [
      {
        run_id: 'run-1',
        agent_name: 'test-agent',
        total_tasks: 1,
        tasks: mockTaskOutputs,
      },
    ];
    mockGetRunDetails.mockResolvedValue(mockRunDetailsResponse);

    const { result } = renderHook(() => useAgentDetails(mockAgentName));

    await act(async () => {
      await result.current.fetchRunDetails(['run-1']);
    });

    expect(mockGetRunDetails).toHaveBeenCalledWith(['run-1']);
    expect(result.current.runTaskDetails.get('run-1')).toEqual(mockTaskOutputs);
  });

  it('should not fetch run details for already cached runs', async () => {
    const mockRunDetailsResponse = [
      {
        run_id: 'run-1',
        agent_name: 'test-agent',
        total_tasks: 1,
        tasks: mockTaskOutputs,
      },
    ];
    mockGetRunDetails.mockResolvedValue(mockRunDetailsResponse);

    const { result } = renderHook(() => useAgentDetails(mockAgentName));

    // First fetch
    await act(async () => {
      await result.current.fetchRunDetails(['run-1']);
    });

    expect(mockGetRunDetails).toHaveBeenCalledTimes(1);

    // Second fetch with same ID - should not call API again
    await act(async () => {
      await result.current.fetchRunDetails(['run-1']);
    });

    expect(mockGetRunDetails).toHaveBeenCalledTimes(1);
  });

  it('should only fetch uncached run details when mixed IDs provided', async () => {
    const mockRunDetailsResponse1 = [
      {
        run_id: 'run-1',
        agent_name: 'test-agent',
        total_tasks: 1,
        tasks: mockTaskOutputs,
      },
    ];
    const mockRunDetailsResponse2 = [
      {
        run_id: 'run-2',
        agent_name: 'test-agent',
        total_tasks: 1,
        tasks: mockTaskOutputs,
      },
    ];
    mockGetRunDetails
      .mockResolvedValueOnce(mockRunDetailsResponse1)
      .mockResolvedValueOnce(mockRunDetailsResponse2);

    const { result } = renderHook(() => useAgentDetails(mockAgentName));

    // First fetch run-1
    await act(async () => {
      await result.current.fetchRunDetails(['run-1']);
    });

    expect(mockGetRunDetails).toHaveBeenCalledWith(['run-1']);

    // Second fetch with run-1 (cached) and run-2 (new)
    await act(async () => {
      await result.current.fetchRunDetails(['run-1', 'run-2']);
    });

    expect(mockGetRunDetails).toHaveBeenCalledWith(['run-2']);
  });

  it('should handle errors when fetching agent details', async () => {
    const consoleError = jest.spyOn(console, 'error').mockImplementation();
    mockGetDetails.mockRejectedValue(new Error('API Error'));

    const { result } = renderHook(() => useAgentDetails(mockAgentName));

    await act(async () => {
      await result.current.openDetails();
    });

    expect(consoleError).toHaveBeenCalled();
    expect(result.current.loading).toBe(false);
    consoleError.mockRestore();
  });

  it('should handle errors when fetching run details', async () => {
    const consoleError = jest.spyOn(console, 'error').mockImplementation();
    mockGetRunDetails.mockRejectedValue(new Error('API Error'));

    const { result } = renderHook(() => useAgentDetails(mockAgentName));

    await act(async () => {
      await result.current.fetchRunDetails(['run-1']);
    });

    expect(consoleError).toHaveBeenCalled();
    expect(result.current.loadingRunDetails.size).toBe(0);
    consoleError.mockRestore();
  });

  it('should track loading state for run details', async () => {
    let resolvePromise: (value: unknown) => void;
    const promise = new Promise(resolve => {
      resolvePromise = resolve;
    });
    mockGetRunDetails.mockReturnValue(promise as Promise<never>);

    const { result } = renderHook(() => useAgentDetails(mockAgentName));

    // Start fetching
    act(() => {
      result.current.fetchRunDetails(['run-1']);
    });

    // Should be loading
    expect(result.current.loadingRunDetails.has('run-1')).toBe(true);

    // Resolve the promise
    await act(async () => {
      resolvePromise!([
        {
          run_id: 'run-1',
          agent_name: 'test-agent',
          total_tasks: 1,
          tasks: [],
        },
      ]);
      await promise;
    });

    // Should no longer be loading
    expect(result.current.loadingRunDetails.has('run-1')).toBe(false);
  });
});
