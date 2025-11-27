import { renderHook, act, waitFor } from '@testing-library/react';
import { useAgentDetails } from './useAgentDetails';
import { getDetails, getRunDetails } from '@/services/dataservice';

// Mock dependencies
jest.mock('react-router-dom', () => ({
    useNavigate: jest.fn(),
}));

jest.mock('@/services/dataservice', () => ({
    getDetails: jest.fn(),
    getRunDetails: jest.fn(),
    getObservabilityLogs: jest.fn(),
}));

describe('useAgentDetails', () => {
    const mockAgentName = 'TestAgent';
    const mockSetActiveAgent = jest.fn();

    beforeEach(() => {
        jest.clearAllMocks();
        (require('react-router-dom').useNavigate as jest.Mock).mockReturnValue(jest.fn());
    });

    it('initializes with default state', () => {
        const { result } = renderHook(() => useAgentDetails(mockAgentName, mockSetActiveAgent));

        expect(result.current.loading).toBe(false);
        expect(result.current.taskDetails).toEqual([]);
        expect(result.current.runDetails).toEqual([]);
        expect(result.current.isOpen).toBe(false);
        expect(result.current.selectedRuns).toEqual([]);
    });

    it('opens details and fetches data', async () => {
        const mockData = [{ run_id: 'run1', agent_name: mockAgentName }];
        (getDetails as jest.Mock).mockResolvedValue(mockData);

        const { result } = renderHook(() => useAgentDetails(mockAgentName, mockSetActiveAgent));

        await act(async () => {
            await result.current.openDetails();
        });

        expect(result.current.loading).toBe(false);
        expect(result.current.runDetails).toEqual(mockData);
        expect(getDetails).toHaveBeenCalledWith(mockAgentName);
    });

    it('toggles details open/close', async () => {
        const mockData = [{ run_id: 'run1' }];
        (getDetails as jest.Mock).mockResolvedValue(mockData);

        const { result } = renderHook(() => useAgentDetails(mockAgentName, mockSetActiveAgent));

        // Open
        await act(async () => {
            await result.current.toggleDetails();
        });
        expect(result.current.isOpen).toBe(true);

        // Close
        act(() => {
            result.current.toggleDetails();
        });
        expect(result.current.isOpen).toBe(false);
    });

    it('toggles run selection', () => {
        const { result } = renderHook(() => useAgentDetails(mockAgentName, mockSetActiveAgent));
        const mockRun = { run_id: 'run1' } as any;

        // Select
        act(() => {
            result.current.toggleRunSelection(mockRun);
        });
        expect(result.current.selectedRuns).toContain('run1');
        expect(mockSetActiveAgent).toHaveBeenCalledWith(mockAgentName);

        // Deselect
        act(() => {
            result.current.toggleRunSelection(mockRun);
        });
        expect(result.current.selectedRuns).not.toContain('run1');
    });

    it('clears selected runs', () => {
        const { result } = renderHook(() => useAgentDetails(mockAgentName, mockSetActiveAgent));
        const mockRun = { run_id: 'run1' } as any;

        act(() => {
            result.current.toggleRunSelection(mockRun);
        });
        expect(result.current.selectedRuns).toHaveLength(1);

        act(() => {
            result.current.clearSelectedRuns();
        });
        expect(result.current.selectedRuns).toHaveLength(0);
    });

    it('fetches run details for unique ids', async () => {
        const mockRunDetails = [{ run_id: 'run1', tasks: [] }];
        (getRunDetails as jest.Mock).mockResolvedValue(mockRunDetails);

        const { result } = renderHook(() => useAgentDetails(mockAgentName, mockSetActiveAgent));

        await act(async () => {
            await result.current.fetchRunDetails(['run1']);
        });

        expect(getRunDetails).toHaveBeenCalledWith(['run1']);
        expect(result.current.runTaskDetails.get('run1')).toEqual([]);
    });

    it('does not fetch run details if already loaded', async () => {
        const mockRunDetails = [{ run_id: 'run1', tasks: [] }];
        (getRunDetails as jest.Mock).mockResolvedValue(mockRunDetails);

        const { result } = renderHook(() => useAgentDetails(mockAgentName, mockSetActiveAgent));

        // First fetch
        await act(async () => {
            await result.current.fetchRunDetails(['run1']);
        });
        expect(getRunDetails).toHaveBeenCalledTimes(1);

        // Second fetch with same ID
        await act(async () => {
            await result.current.fetchRunDetails(['run1']);
        });
        expect(getRunDetails).toHaveBeenCalledTimes(1); // Should not increase
    });

    it('handles error when opening details', async () => {
        const consoleSpy = jest.spyOn(console, 'error').mockImplementation(() => { });
        (getDetails as jest.Mock).mockRejectedValue(new Error('Fetch error'));

        const { result } = renderHook(() => useAgentDetails(mockAgentName, mockSetActiveAgent));

        await act(async () => {
            await result.current.openDetails();
        });

        expect(result.current.loading).toBe(false);
        expect(consoleSpy).toHaveBeenCalledWith(expect.any(Error));
        consoleSpy.mockRestore();
    });

    it('handles error when fetching run details', async () => {
        const consoleSpy = jest.spyOn(console, 'error').mockImplementation(() => { });
        (getRunDetails as jest.Mock).mockRejectedValue(new Error('Fetch error'));

        const { result } = renderHook(() => useAgentDetails(mockAgentName, mockSetActiveAgent));

        await act(async () => {
            await result.current.fetchRunDetails(['run1']);
        });

        expect(consoleSpy).toHaveBeenCalledWith('Error fetching run details:', expect.any(Error));
        consoleSpy.mockRestore();
    });

    it('navigates to compare page when runs are selected', () => {
        const mockNavigate = jest.fn();
        (require('react-router-dom').useNavigate as jest.Mock).mockReturnValue(mockNavigate);

        const { result } = renderHook(() => useAgentDetails(mockAgentName, mockSetActiveAgent));
        const mockRun = { run_id: 'run1' } as any;

        act(() => {
            result.current.toggleRunSelection(mockRun);
        });

        act(() => {
            result.current.compareSelected();
        });

        expect(mockNavigate).toHaveBeenCalledWith({
            pathname: '/compare',
            search: `?agent=${mockAgentName}&runs=run1`,
        });
    });

    it('does not navigate if no runs selected', () => {
        const mockNavigate = jest.fn();
        (require('react-router-dom').useNavigate as jest.Mock).mockReturnValue(mockNavigate);

        const { result } = renderHook(() => useAgentDetails(mockAgentName, mockSetActiveAgent));

        act(() => {
            result.current.compareSelected();
        });

        expect(mockNavigate).not.toHaveBeenCalled();
    });
});
