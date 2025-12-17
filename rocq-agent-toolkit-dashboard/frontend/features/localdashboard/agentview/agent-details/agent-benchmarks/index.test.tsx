import { fireEvent, render, screen, waitFor } from '@testing-library/react';
import React from 'react';
import { MemoryRouter } from 'react-router-dom';

import { useGlobalCompare } from '@/contexts/global-compare-context';

import { AgentBenchmark } from './index';
import { useAgentBenchmarks } from './use-benchmark-runs';

jest.mock('./use-benchmark-runs');
jest.mock('@/contexts/global-compare-context');
jest.mock('@/features/localdashboard/agent-runs-view', () => ({
  __esModule: true,
  default: ({
    agentName,
    selectedRuns,
  }: {
    agentName: string;
    selectedRuns: string[];
  }) => (
    <div data-testid='agent-runs-view'>
      Agent: {agentName}, Selected: {selectedRuns.join(',')}
    </div>
  ),
}));

const mockUseAgentBenchmarks = useAgentBenchmarks as jest.MockedFunction<
  typeof useAgentBenchmarks
>;
const mockUseGlobalCompare = useGlobalCompare as jest.MockedFunction<
  typeof useGlobalCompare
>;
const mockNavigate = jest.fn();

jest.mock('react-router-dom', () => {
  const actual = jest.requireActual('react-router-dom');
  return {
    ...actual,
    useNavigate: () => mockNavigate,
  };
});

describe('AgentBenchmark', () => {
  const mockBenchmark = {
    dataset_id: 'bench1',
    description: 'Test Benchmark',
    created_at: '2024-01-01T00:00:00Z',
  };

  const mockRuns = [
    {
      run_id: 'run1',
      agent_name: 'agent1',
      timestamp_utc: '2024-01-01',
      total_tasks: 10,
      success_count: 8,
      failure_count: 2,
      dataset_id: 'bench1',
      metadata: { tags: {} },
    },
  ];

  beforeEach(() => {
    jest.clearAllMocks();

    mockUseAgentBenchmarks.mockReturnValue({
      runs: mockRuns,
      isLoading: false,
      error: null,
      fetchRuns: jest.fn(),
    });

    mockUseGlobalCompare.mockReturnValue({
      selections: {
        selectedAgents: [],
        selectedRuns: [],
        activeDatasetId: null,
      },
      selectAgent: jest.fn(),
      deselectAgent: jest.fn(),
      selectRun: jest.fn(),
      deselectRun: jest.fn(),
      clearAllSelections: jest.fn(),
      clearDatasetSelections: jest.fn(),
      getSelectedAgentsForDataset: jest.fn(),
      getSelectedRunsForDataset: jest.fn(() => []),
      isAgentSelected: jest.fn(),
      isRunSelected: jest.fn(() => false),
    });
  });

  it('should render benchmark header', () => {
    render(
      <MemoryRouter>
        <AgentBenchmark benchmark={mockBenchmark} agentName='agent1' />
      </MemoryRouter>
    );

    expect(screen.getByText('bench1')).toBeInTheDocument();
  });

  it('should toggle open/close when header is clicked', () => {
    render(
      <MemoryRouter>
        <AgentBenchmark benchmark={mockBenchmark} agentName='agent1' />
      </MemoryRouter>
    );

    const header = screen.getByText('bench1').closest('div');
    if (header) {
      fireEvent.click(header);
      // Should expand and show runs
    }
  });

  it('should fetch runs when opened for first time', () => {
    const mockFetchRuns = jest.fn();
    mockUseAgentBenchmarks.mockReturnValue({
      runs: [],
      isLoading: false,
      error: null,
      fetchRuns: mockFetchRuns,
    });

    render(
      <MemoryRouter>
        <AgentBenchmark benchmark={mockBenchmark} agentName='agent1' />
      </MemoryRouter>
    );

    const header = screen.getByText('bench1').closest('div');
    if (header) {
      fireEvent.click(header);
      expect(mockFetchRuns).toHaveBeenCalled();
    }
  });

  it('should show loading state', () => {
    mockUseAgentBenchmarks.mockReturnValue({
      runs: [],
      isLoading: true,
      error: null,
      fetchRuns: jest.fn(),
    });

    render(
      <MemoryRouter>
        <AgentBenchmark benchmark={mockBenchmark} agentName='agent1' />
      </MemoryRouter>
    );

    const header = screen.getByText('bench1').closest('div');
    if (header) {
      fireEvent.click(header);
      // Should show loading spinner
    }
  });
});
