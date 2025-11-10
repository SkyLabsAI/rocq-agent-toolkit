import { renderHook, act } from '@testing-library/react';
import { useAgentDetails } from '../useAgentDetails';
import * as dataservice from '@/services/dataservice';

// Mock the dataservice module
jest.mock('@/services/dataservice');
const mockGetDetails = dataservice.getDetails as jest.MockedFunction<typeof dataservice.getDetails>;
const mockGetRunDetails = dataservice.getRunDetails as jest.MockedFunction<typeof dataservice.getRunDetails>;
const mockGetObservabilityLogs = dataservice.getObservabilityLogs as jest.MockedFunction<typeof dataservice.getObservabilityLogs>;

// Mock Next.js router
const mockPush = jest.fn();
jest.mock('next/navigation', () => ({
  useRouter: () => ({
    push: mockPush,
  }),
}));

describe('useAgentDetails', () => {
  const agentName = 'TestAgent';

  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('should initialize with default values', () => {
    const { result } = renderHook(() => useAgentDetails(agentName));

    expect(result.current.loading).toBe(false);
    expect(result.current.taskDetails).toEqual([]);
    expect(result.current.runDetails).toEqual([]);
    expect(result.current.isOpen).toBe(false);
    expect(result.current.modalState.isOpen).toBe(false);
    expect(result.current.selectedRuns).toEqual([]);
    expect(result.current.expandedRuns.size).toBe(0);
  });

  it('should toggle details and fetch data', async () => {
    const mockRunDetails = [
      {
        run_id: 'run1',
        agent_name: agentName,
        timestamp_utc: '2023-01-01T00:00:00Z',
        total_tasks: 5,
        success_count: 3,
        failure_count: 2,
      },
    ];

    mockGetDetails.mockResolvedValue(mockRunDetails);

    const { result } = renderHook(() => useAgentDetails(agentName));

    await act(async () => {
      await result.current.toggleDetails();
    });

    expect(mockGetDetails).toHaveBeenCalledWith(agentName);
    expect(result.current.isOpen).toBe(true);
    expect(result.current.runDetails).toEqual(mockRunDetails);
    expect(result.current.loading).toBe(false);
  });

  it('should handle toggle details error', async () => {
    const consoleSpy = jest.spyOn(console, 'error').mockImplementation();
    mockGetDetails.mockRejectedValue(new Error('API Error'));

    const { result } = renderHook(() => useAgentDetails(agentName));

    await act(async () => {
      await result.current.toggleDetails();
    });

    expect(consoleSpy).toHaveBeenCalledWith(new Error('API Error'));
    expect(result.current.loading).toBe(false);
    
    consoleSpy.mockRestore();
  });

  it('should open code modal with logs', async () => {
    const mockTask = {
      run_id: 'run1',
      task_id: 'task1',
      agent_name: agentName,
      status: 'Success' as const,
      timestamp_utc: '2023-01-01T00:00:00Z',
      task_kind: 'FullProofTask' as const,
      results: null,
      metrics: {
        llm_invocation_count: 1,
        token_counts: { input_tokens: 100, output_tokens: 50, total_tokens: 150 },
        resource_usage: { execution_time_sec: 1.5, cpu_time_sec: 1.0, gpu_time_sec: 0.5 },
        custom: null,
      },
    };

    const mockLogs = { step1: 'Initialize', step2: 'Process' };
    mockGetObservabilityLogs.mockResolvedValue(mockLogs);

    const { result } = renderHook(() => useAgentDetails(agentName));

    await act(async () => {
      await result.current.openCodeModal(mockTask);
    });

    expect(mockGetObservabilityLogs).toHaveBeenCalledWith('run1', 'task1');
    expect(result.current.modalState.isOpen).toBe(true);
    expect(result.current.modalState.selectedTask).toEqual(mockTask);
    expect(result.current.modalState.logs).toEqual(mockLogs);
    expect(result.current.loadingLogs).toBe(null);
  });

  it('should handle code modal error', async () => {
    const consoleSpy = jest.spyOn(console, 'error').mockImplementation();
    const mockTask = {
      run_id: 'run1',
      task_id: 'task1',
      agent_name: agentName,
      status: 'Success' as const,
      timestamp_utc: '2023-01-01T00:00:00Z',
      task_kind: 'FullProofTask' as const,
      results: null,
      metrics: {
        llm_invocation_count: 1,
        token_counts: { input_tokens: 100, output_tokens: 50, total_tokens: 150 },
        resource_usage: { execution_time_sec: 1.5, cpu_time_sec: 1.0, gpu_time_sec: 0.5 },
        custom: null,
      },
    };

    mockGetObservabilityLogs.mockRejectedValue(new Error('Log fetch failed'));

    const { result } = renderHook(() => useAgentDetails(agentName));

    await act(async () => {
      await result.current.openCodeModal(mockTask);
    });

    expect(result.current.modalState.isOpen).toBe(true);
    expect(result.current.modalState.logs).toEqual({ error: 'Failed to load logs' });
    expect(consoleSpy).toHaveBeenCalledWith('Error fetching observability logs:', new Error('Log fetch failed'));
    
    consoleSpy.mockRestore();
  });

  it('should close modal', () => {
    const { result } = renderHook(() => useAgentDetails(agentName));

    // First open modal
    act(() => {
      result.current.closeModal();
    });

    expect(result.current.modalState.isOpen).toBe(false);
    expect(result.current.modalState.selectedTask).toBe(null);
    expect(result.current.modalState.logs).toBe(null);
  });

  it('should toggle run selection', () => {
    const { result } = renderHook(() => useAgentDetails(agentName));

    act(() => {
      result.current.toggleRunSelection('run1');
    });

    expect(result.current.selectedRuns).toContain('run1');

    act(() => {
      result.current.toggleRunSelection('run2');
    });

    expect(result.current.selectedRuns).toContain('run2');

    // Toggle off
    act(() => {
      result.current.toggleRunSelection('run1');
    });

    expect(result.current.selectedRuns).not.toContain('run1');
    expect(result.current.selectedRuns).toContain('run2');
  });

  it('should clear selected runs', () => {
    const { result } = renderHook(() => useAgentDetails(agentName));

    act(() => {
      result.current.toggleRunSelection('run1');
      result.current.toggleRunSelection('run2');
    });

    expect(result.current.selectedRuns).toHaveLength(2);

    act(() => {
      result.current.clearSelectedRuns();
    });

    expect(result.current.selectedRuns).toHaveLength(0);
  });

  it('should navigate to compare page', () => {
    const { result } = renderHook(() => useAgentDetails(agentName));

    act(() => {
      result.current.toggleRunSelection('run1');
      result.current.toggleRunSelection('run2');
    });

    act(() => {
      result.current.compareSelected();
    });

    expect(mockPush).toHaveBeenCalledWith('/admin/compare?agent=TestAgent&runs=run1%2Crun2');
  });
});