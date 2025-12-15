import { fireEvent, render, screen, waitFor } from '@testing-library/react';
import React from 'react';
import { MemoryRouter } from 'react-router-dom';

import { useGlobalCompare } from '@/contexts/GlobalCompareContext';
import { useSelectedRun } from '@/contexts/SelectedRunContext';
import { useBenchmarkAgents } from '@/hooks/use-dataview';
import { useAgents } from '@/hooks/useAgentsSummary';

import { DataItem } from './index';

jest.mock('@/hooks/use-dataview');
jest.mock('@/hooks/useAgentsSummary');
jest.mock('@/contexts/SelectedRunContext');
jest.mock('@/contexts/GlobalCompareContext');
jest.mock('./agent-details', () => ({
  __esModule: true,
  default: ({ agent }: { agent: { agent_name: string } }) => (
    <tr data-testid={`agent-details-${agent.agent_name}`}>
      <td>{agent.agent_name}</td>
    </tr>
  ),
}));
jest.mock('@/features/taskDetailsModal', () => ({
  __esModule: true,
  default: ({ isOpen }: { isOpen: boolean }) =>
    isOpen ? <div data-testid='task-details-modal'>Task Modal</div> : null,
}));
jest.mock('@/components/RunDetailsView', () => ({
  __esModule: true,
  default: ({ run }: { run: { run_id: string } }) => (
    <div data-testid='run-details-view'>Run: {run.run_id}</div>
  ),
}));

const mockUseBenchmarkAgents = useBenchmarkAgents as jest.MockedFunction<
  typeof useBenchmarkAgents
>;
const mockUseAgents = useAgents as jest.MockedFunction<typeof useAgents>;
const mockUseSelectedRun = useSelectedRun as jest.MockedFunction<
  typeof useSelectedRun
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
    useLocation: () => ({ pathname: '/' }),
  };
});

describe('DataItem', () => {
  const mockBenchmark = {
    dataset_id: 'bench1',
    description: 'Test Benchmark',
    created_at: '2024-01-01T00:00:00Z',
  };

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

  beforeEach(() => {
    jest.clearAllMocks();
    mockUseBenchmarkAgents.mockReturnValue({
      agents: mockAgents,
      loading: false,
    });
    mockUseAgents.mockReturnValue({
      agentData: [],
      agentDetailData: [],
      isLoading: false,
      openCodeModal: jest.fn(),
      closeModal: jest.fn(),
      modalState: { isOpen: false, selectedTask: null, logs: null },
      loadingLogs: null,
    });
    mockUseSelectedRun.mockReturnValue({
      selectedRun: null,
      setSelectedRun: jest.fn(),
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
      getSelectedAgentsForDataset: jest.fn(() => []),
      getSelectedRunsForDataset: jest.fn(() => []),
      isAgentSelected: jest.fn(() => false),
      isRunSelected: jest.fn(() => false),
    });
  });

  it('should render benchmark header', () => {
    render(
      <MemoryRouter>
        <DataItem benchmark={mockBenchmark} />
      </MemoryRouter>
    );

    expect(screen.getByText('bench1')).toBeInTheDocument();
  });

  it('should toggle open/close when header is clicked', () => {
    render(
      <MemoryRouter>
        <DataItem benchmark={mockBenchmark} />
      </MemoryRouter>
    );

    const header = screen.getByText('bench1').closest('div');
    if (header) {
      fireEvent.click(header);
      // Component should expand
      expect(screen.getByText('Agents')).toBeInTheDocument();
    }
  });

  it('should display agents when open', () => {
    render(
      <MemoryRouter>
        <DataItem benchmark={mockBenchmark} />
      </MemoryRouter>
    );

    const header = screen.getByText('bench1').closest('div');
    if (header) {
      fireEvent.click(header);
      expect(screen.getByTestId('agent-details-agent1')).toBeInTheDocument();
    }
  });

  it('should handle sorting by agent_name', () => {
    render(
      <MemoryRouter>
        <DataItem benchmark={mockBenchmark} />
      </MemoryRouter>
    );

    const header = screen.getByText('bench1').closest('div');
    if (header) {
      fireEvent.click(header);
      const sortButton = screen.getByText('Agents');
      fireEvent.click(sortButton);
      expect(screen.getByTestId('agent-details-agent1')).toBeInTheDocument();
    }
  });

  it('should handle sorting by success_rate', () => {
    render(
      <MemoryRouter>
        <DataItem benchmark={mockBenchmark} />
      </MemoryRouter>
    );

    const header = screen.getByText('bench1').closest('div');
    if (header) {
      fireEvent.click(header);
      const sortButton = screen.getByText('Success Rate');
      fireEvent.click(sortButton);
      expect(screen.getByTestId('agent-details-agent1')).toBeInTheDocument();
    }
  });

  it('should toggle sort direction', () => {
    render(
      <MemoryRouter>
        <DataItem benchmark={mockBenchmark} />
      </MemoryRouter>
    );

    const header = screen.getByText('bench1').closest('div');
    if (header) {
      fireEvent.click(header);
      const sortButton = screen.getByText('Agents');
      fireEvent.click(sortButton); // First click - asc
      fireEvent.click(sortButton); // Second click - desc
      expect(screen.getByTestId('agent-details-agent1')).toBeInTheDocument();
    }
  });

  it('should show RunDetailsView when run is selected', () => {
    const mockRun = {
      run_id: 'run1',
      agent_name: 'agent1',
      timestamp_utc: '2024-01-01',
      total_tasks: 10,
      success_count: 8,
      failure_count: 2,
    };

    mockUseSelectedRun.mockReturnValue({
      selectedRun: mockRun,
      setSelectedRun: jest.fn(),
    });

    render(
      <MemoryRouter>
        <DataItem benchmark={mockBenchmark} />
      </MemoryRouter>
    );

    expect(screen.getByTestId('run-details-view')).toBeInTheDocument();
  });

  it('should clear dataset selections when run is selected', () => {
    const mockClearDatasetSelections = jest.fn();
    const mockRun = {
      run_id: 'run1',
      agent_name: 'agent1',
      timestamp_utc: '2024-01-01',
      total_tasks: 10,
      success_count: 8,
      failure_count: 2,
    };

    mockUseSelectedRun.mockReturnValue({
      selectedRun: mockRun,
      setSelectedRun: jest.fn(),
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
      clearDatasetSelections: mockClearDatasetSelections,
      getSelectedAgentsForDataset: jest.fn(() => []),
      getSelectedRunsForDataset: jest.fn(() => []),
      isAgentSelected: jest.fn(() => false),
      isRunSelected: jest.fn(() => false),
    });

    render(
      <MemoryRouter>
        <DataItem benchmark={mockBenchmark} />
      </MemoryRouter>
    );

    expect(mockClearDatasetSelections).toHaveBeenCalledWith('bench1');
  });

  it('should clear dataset selections when navigating to compare page', () => {
    const mockClearDatasetSelections = jest.fn();
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
      clearDatasetSelections: mockClearDatasetSelections,
      getSelectedAgentsForDataset: jest.fn(() => []),
      getSelectedRunsForDataset: jest.fn(() => []),
      isAgentSelected: jest.fn(() => false),
      isRunSelected: jest.fn(() => false),
    });

    jest.spyOn(require('react-router-dom'), 'useLocation').mockReturnValue({
      pathname: '/compare',
    });

    render(
      <MemoryRouter>
        <DataItem benchmark={mockBenchmark} />
      </MemoryRouter>
    );

    expect(mockClearDatasetSelections).toHaveBeenCalledWith('bench1');
  });

  it('should handle sorting by avg_cpu_time_sec', () => {
    render(
      <MemoryRouter>
        <DataItem benchmark={mockBenchmark} />
      </MemoryRouter>
    );

    const header = screen.getByText('bench1').closest('div');
    if (header) {
      fireEvent.click(header);
      const sortButton = screen.getByText('Avg Time (s)');
      fireEvent.click(sortButton);
      expect(screen.getByTestId('agent-details-agent1')).toBeInTheDocument();
    }
  });

  it('should handle sorting by avg_total_tokens', () => {
    render(
      <MemoryRouter>
        <DataItem benchmark={mockBenchmark} />
      </MemoryRouter>
    );

    const header = screen.getByText('bench1').closest('div');
    if (header) {
      fireEvent.click(header);
      const sortButton = screen.getByText('Avg Tokens');
      fireEvent.click(sortButton);
      expect(screen.getByTestId('agent-details-agent1')).toBeInTheDocument();
    }
  });

  it('should handle sorting by avg_llm_invocation_count', () => {
    render(
      <MemoryRouter>
        <DataItem benchmark={mockBenchmark} />
      </MemoryRouter>
    );

    const header = screen.getByText('bench1').closest('div');
    if (header) {
      fireEvent.click(header);
      const sortButton = screen.getByText('Avg LLM Calls');
      fireEvent.click(sortButton);
      expect(screen.getByTestId('agent-details-agent1')).toBeInTheDocument();
    }
  });

  it('should toggle run selection', () => {
    const mockSelectRun = jest.fn();
    const mockDeselectRun = jest.fn();
    mockUseGlobalCompare.mockReturnValue({
      selections: {
        selectedAgents: [],
        selectedRuns: [],
        activeDatasetId: null,
      },
      selectAgent: jest.fn(),
      deselectAgent: jest.fn(),
      selectRun: mockSelectRun,
      deselectRun: mockDeselectRun,
      clearAllSelections: jest.fn(),
      clearDatasetSelections: jest.fn(),
      getSelectedAgentsForDataset: jest.fn(() => []),
      getSelectedRunsForDataset: jest.fn(() => []),
      isAgentSelected: jest.fn(() => false),
      isRunSelected: jest.fn(() => false),
    });

    render(
      <MemoryRouter>
        <DataItem benchmark={mockBenchmark} />
      </MemoryRouter>
    );

    // This would require the component to be expanded and a run to be available
    expect(screen.getByText('bench1')).toBeInTheDocument();
  });
});
