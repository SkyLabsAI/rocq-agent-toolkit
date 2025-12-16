import { act, renderHook } from '@testing-library/react';

import { getDetailsForDataset, getRunDetails } from '@/services/dataservice';
import { type AgentRun, type TaskOutput } from '@/types/types';

import { useDatasetAgentDetails } from './use-data-set-agent-details';

// Mock the dataservice
jest.mock('@/services/dataservice', () => ({
  getDetailsForDataset: jest.fn(),
  getRunDetails: jest.fn(),
}));

const mockGetDetailsForDataset = getDetailsForDataset as jest.MockedFunction<
  typeof getDetailsForDataset
>;
const mockGetRunDetails = getRunDetails as jest.MockedFunction<
  typeof getRunDetails
>;

describe('useDatasetAgentDetails', () => {
  const mockDatasetId = 'dataset-1';
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
    const { result } = renderHook(() =>
      useDatasetAgentDetails(mockDatasetId, mockAgentName)
    );

    expect(result.current.loading).toBe(false);
    expect(result.current.isOpen).toBe(false);
    expect(result.current.taskDetails).toEqual([]);
    expect(result.current.runDetails).toEqual([]);
    expect(result.current.runTaskDetails.size).toBe(0);
  });

  it('should fetch agent details for specific dataset on openDetails', async () => {
    mockGetDetailsForDataset.mockResolvedValue(mockRunDetails);

    const { result } = renderHook(() =>
      useDatasetAgentDetails(mockDatasetId, mockAgentName)
    );

    await act(async () => {
      await result.current.openDetails();
    });

    expect(mockGetDetailsForDataset).toHaveBeenCalledWith(
      mockDatasetId,
      mockAgentName
    );
    expect(result.current.runDetails).toEqual(mockRunDetails);
    expect(result.current.loading).toBe(false);
  });

  it('should toggle details open and closed', async () => {
    mockGetDetailsForDataset.mockResolvedValue(mockRunDetails);

    const { result } = renderHook(() =>
      useDatasetAgentDetails(mockDatasetId, mockAgentName)
    );

    expect(result.current.isOpen).toBe(false);

    // Open details
    await act(async () => {
      await result.current.toggleDetails();
    });

    expect(result.current.isOpen).toBe(true);

    // Close details
    await act(async () => {
      result.current.toggleDetails();
    });

    expect(result.current.isOpen).toBe(false);
  });

  it('should fetch run details and cache them', async () => {
    const mockRunDetailsResponse = [
      {
        run_id: 'run-1',
        agent_name: 'test-agent',
        total_tasks: 1,
        tasks: mockTaskOutputs,
      },
    ];
    mockGetRunDetails.mockResolvedValue(mockRunDetailsResponse);

    const { result } = renderHook(() =>
      useDatasetAgentDetails(mockDatasetId, mockAgentName)
    );

    await act(async () => {
      await result.current.fetchRunDetails(['run-1']);
    });

    expect(mockGetRunDetails).toHaveBeenCalledWith(['run-1']);
    expect(result.current.runTaskDetails.get('run-1')).toEqual(mockTaskOutputs);
  });

  it('should not refetch cached run details', async () => {
    const mockRunDetailsResponse = [
      {
        run_id: 'run-1',
        agent_name: 'test-agent',
        total_tasks: 1,
        tasks: mockTaskOutputs,
      },
    ];
    mockGetRunDetails.mockResolvedValue(mockRunDetailsResponse);

    const { result } = renderHook(() =>
      useDatasetAgentDetails(mockDatasetId, mockAgentName)
    );

    await act(async () => {
      await result.current.fetchRunDetails(['run-1']);
    });

    // Try to fetch same run again
    await act(async () => {
      await result.current.fetchRunDetails(['run-1']);
    });

    // Should only be called once
    expect(mockGetRunDetails).toHaveBeenCalledTimes(1);
  });

  it('should handle errors gracefully', async () => {
    const consoleError = jest.spyOn(console, 'error').mockImplementation(() => {});
    mockGetDetailsForDataset.mockRejectedValue(new Error('API Error'));

    const { result } = renderHook(() =>
      useDatasetAgentDetails(mockDatasetId, mockAgentName)
    );

    await act(async () => {
      await result.current.openDetails();
    });

    // Hook does not expose error; assert loading stops and details unchanged
    expect(result.current.loading).toBe(false);
    expect(result.current.runDetails).toEqual([]);
    consoleError.mockRestore();
  });

  it('should clear task details when opening new details', async () => {
    mockGetDetailsForDataset.mockResolvedValue(mockRunDetails);

    const { result } = renderHook(() =>
      useDatasetAgentDetails(mockDatasetId, mockAgentName)
    );

    await act(async () => {
      await result.current.openDetails();
    });

    // taskDetails should be cleared (empty array)
    expect(result.current.taskDetails).toEqual([]);
  });
});
