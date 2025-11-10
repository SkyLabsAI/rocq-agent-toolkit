import { renderHook, act } from '@testing-library/react';
import { useAdminDashboard } from '../useAdminDashboard';
import * as dataservice from '@/services/dataservice';

// Mock the dataservice module
jest.mock('@/services/dataservice');
const mockGetData = dataservice.getData as jest.MockedFunction<typeof dataservice.getData>;
const mockRefreshData = dataservice.refreshData as jest.MockedFunction<typeof dataservice.refreshData>;

describe('useAdminDashboard', () => {
  beforeEach(() => {
    jest.clearAllMocks();
    jest.useFakeTimers();
  });

  afterEach(() => {
    jest.runOnlyPendingTimers();
    jest.useRealTimers();
  });

  it('should fetch data on mount', async () => {
    const mockAgentData = [
      { agent_name: 'TestAgent1', total_runs: 5 },
      { agent_name: 'TestAgent2', total_runs: 3 },
    ];
    
    mockGetData.mockResolvedValue(mockAgentData);

    const { result } = renderHook(() => useAdminDashboard());

    // Wait for the useEffect to complete
    await act(async () => {
      // Flush promises
      await Promise.resolve();
    });

    expect(mockGetData).toHaveBeenCalledTimes(1);
    expect(result.current.agentData).toEqual(mockAgentData);
  });

  it('should handle refresh successfully', async () => {
    const mockAgentData = [{ agent_name: 'TestAgent', total_runs: 2 }];
    const mockRefreshResponse = {
      success: true,
      message: 'Data refreshed successfully',
      total_tasks: 10,
      total_agents: 1,
    };

    mockGetData.mockResolvedValue(mockAgentData);
    mockRefreshData.mockResolvedValue(mockRefreshResponse);

    const { result } = renderHook(() => useAdminDashboard());

    await act(async () => {
      await result.current.handleRefresh();
    });

    expect(mockRefreshData).toHaveBeenCalledTimes(1);
    expect(result.current.refreshMessage).toBe('Data refreshed successfully');
    expect(result.current.isRefreshing).toBe(false);
  });

  it('should handle refresh error', async () => {
    mockRefreshData.mockRejectedValue(new Error('Network error'));

    const { result } = renderHook(() => useAdminDashboard());

    await act(async () => {
      await result.current.handleRefresh();
    });

    expect(result.current.refreshMessage).toBe('Error refreshing data. Please try again.');
    expect(result.current.isRefreshing).toBe(false);
  });

  it('should clear refresh message after 3 seconds', async () => {
    const mockRefreshResponse = {
      success: true,
      message: 'Success!',
      total_tasks: 5,
      total_agents: 1,
    };

    mockRefreshData.mockResolvedValue(mockRefreshResponse);
    mockGetData.mockResolvedValue([]);

    const { result } = renderHook(() => useAdminDashboard());

    await act(async () => {
      await result.current.handleRefresh();
    });

    expect(result.current.refreshMessage).toBe('Success!');

    // Fast-forward time by 3 seconds
    await act(async () => {
      jest.advanceTimersByTime(3000);
    });

    expect(result.current.refreshMessage).toBe('');
  });

  it('should set isRefreshing to true during refresh', async () => {
    let resolveRefresh: (value: { success: boolean; message: string; total_tasks: number; total_agents: number }) => void;
    const refreshPromise = new Promise<{ success: boolean; message: string; total_tasks: number; total_agents: number }>(resolve => {
      resolveRefresh = resolve;
    });
    mockRefreshData.mockImplementation(() => refreshPromise);

    const { result } = renderHook(() => useAdminDashboard());

    act(() => {
      result.current.handleRefresh();
    });

    expect(result.current.isRefreshing).toBe(true);

    await act(async () => {
      resolveRefresh({
        success: true,
        message: 'Done',
        total_tasks: 1,
        total_agents: 1,
      });
      await refreshPromise;
    });

    expect(result.current.isRefreshing).toBe(false);
  });
});