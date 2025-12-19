import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';
import { MemoryRouter } from 'react-router-dom';

import { useGlobalCompare } from '@/contexts/global-compare-context';

import { GlobalStickyCompareBar } from './global-sticky-compare-bar';

jest.mock('@/contexts/global-compare-context');
jest.mock('@/components/sticky-compare-bar', () => ({
  __esModule: true,
  default: ({
    selectedItems,
    onCompareSelected,
    onClearSelection,
    attribute,
  }: {
    selectedItems: string[];
    onCompareSelected: () => void;
    onClearSelection: () => void;
    attribute: string;
  }) => (
    <div data-testid='sticky-compare-bar'>
      <div data-testid='items'>{selectedItems.join(',')}</div>
      <div data-testid='attribute'>{attribute}</div>
      <button onClick={onCompareSelected}>Compare</button>
      <button onClick={onClearSelection}>Clear</button>
    </div>
  ),
}));

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

describe('GlobalStickyCompareBar', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('should render nothing when no selections', () => {
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
      getSelectedRunsForDataset: jest.fn(),
      isAgentSelected: jest.fn(),
      isRunSelected: jest.fn(),
    });

    const { container } = render(
      <MemoryRouter>
        <GlobalStickyCompareBar />
      </MemoryRouter>
    );

    expect(container.firstChild).toBeNull();
  });

  it('should render agent comparison bar when agents are selected', () => {
    const mockClearAllSelections = jest.fn();
    mockUseGlobalCompare.mockReturnValue({
      selections: {
        selectedAgents: [
          { agentName: 'agent1', datasetId: 'bench1' },
          { agentName: 'agent2', datasetId: 'bench1' },
        ],
        selectedRuns: [],
        activeDatasetId: 'bench1',
      },
      selectAgent: jest.fn(),
      deselectAgent: jest.fn(),
      selectRun: jest.fn(),
      deselectRun: jest.fn(),
      clearAllSelections: mockClearAllSelections,
      clearDatasetSelections: jest.fn(),
      getSelectedAgentsForDataset: jest.fn(),
      getSelectedRunsForDataset: jest.fn(),
      isAgentSelected: jest.fn(),
      isRunSelected: jest.fn(),
    });

    render(
      <MemoryRouter>
        <GlobalStickyCompareBar />
      </MemoryRouter>
    );

    expect(screen.getByTestId('sticky-compare-bar')).toBeInTheDocument();
    expect(screen.getByTestId('items')).toHaveTextContent('agent1,agent2');
    expect(screen.getByTestId('attribute')).toHaveTextContent('Agents');
  });

  it('should render run comparison bar when runs are selected', () => {
    const mockClearAllSelections = jest.fn();
    mockUseGlobalCompare.mockReturnValue({
      selections: {
        selectedAgents: [],
        selectedRuns: [
          { runId: 'run1', datasetId: 'bench1' },
          { runId: 'run2', datasetId: 'bench1' },
        ],
        activeDatasetId: 'bench1',
      },
      selectAgent: jest.fn(),
      deselectAgent: jest.fn(),
      selectRun: jest.fn(),
      deselectRun: jest.fn(),
      clearAllSelections: mockClearAllSelections,
      clearDatasetSelections: jest.fn(),
      getSelectedAgentsForDataset: jest.fn(),
      getSelectedRunsForDataset: jest.fn(),
      isAgentSelected: jest.fn(),
      isRunSelected: jest.fn(),
    });

    render(
      <MemoryRouter>
        <GlobalStickyCompareBar />
      </MemoryRouter>
    );

    expect(screen.getByTestId('sticky-compare-bar')).toBeInTheDocument();
    expect(screen.getByTestId('items')).toHaveTextContent('run1,run2');
    expect(screen.getByTestId('attribute')).toHaveTextContent('Runs');
  });

  it('should navigate to agent compare page when compare is clicked', () => {
    mockUseGlobalCompare.mockReturnValue({
      selections: {
        selectedAgents: [{ agentName: 'agent1', datasetId: 'bench1' }],
        selectedRuns: [],
        activeDatasetId: 'bench1',
      },
      selectAgent: jest.fn(),
      deselectAgent: jest.fn(),
      selectRun: jest.fn(),
      deselectRun: jest.fn(),
      clearAllSelections: jest.fn(),
      clearDatasetSelections: jest.fn(),
      getSelectedAgentsForDataset: jest.fn(),
      getSelectedRunsForDataset: jest.fn(),
      isAgentSelected: jest.fn(),
      isRunSelected: jest.fn(),
    });

    render(
      <MemoryRouter>
        <GlobalStickyCompareBar />
      </MemoryRouter>
    );

    fireEvent.click(screen.getByText('Compare'));

    expect(mockNavigate).toHaveBeenCalledWith({
      pathname: '/compare/agents',
      search: '?agents=agent1',
    });
  });

  it('should navigate to run compare page when compare is clicked', () => {
    mockUseGlobalCompare.mockReturnValue({
      selections: {
        selectedAgents: [],
        selectedRuns: [{ runId: 'run1', datasetId: 'bench1' }],
        activeDatasetId: 'bench1',
      },
      selectAgent: jest.fn(),
      deselectAgent: jest.fn(),
      selectRun: jest.fn(),
      deselectRun: jest.fn(),
      clearAllSelections: jest.fn(),
      clearDatasetSelections: jest.fn(),
      getSelectedAgentsForDataset: jest.fn(),
      getSelectedRunsForDataset: jest.fn(),
      isAgentSelected: jest.fn(),
      isRunSelected: jest.fn(),
    });

    render(
      <MemoryRouter>
        <GlobalStickyCompareBar />
      </MemoryRouter>
    );

    fireEvent.click(screen.getByText('Compare'));

    expect(mockNavigate).toHaveBeenCalledWith({
      pathname: '/compare',
      search: '?runs=run1',
    });
  });

  it('should call clearAllSelections when clear is clicked', () => {
    const mockClearAllSelections = jest.fn();
    mockUseGlobalCompare.mockReturnValue({
      selections: {
        selectedAgents: [{ agentName: 'agent1', datasetId: 'bench1' }],
        selectedRuns: [],
        activeDatasetId: 'bench1',
      },
      selectAgent: jest.fn(),
      deselectAgent: jest.fn(),
      selectRun: jest.fn(),
      deselectRun: jest.fn(),
      clearAllSelections: mockClearAllSelections,
      clearDatasetSelections: jest.fn(),
      getSelectedAgentsForDataset: jest.fn(),
      getSelectedRunsForDataset: jest.fn(),
      isAgentSelected: jest.fn(),
      isRunSelected: jest.fn(),
    });

    render(
      <MemoryRouter>
        <GlobalStickyCompareBar />
      </MemoryRouter>
    );

    fireEvent.click(screen.getByText('Clear'));

    expect(mockClearAllSelections).toHaveBeenCalledTimes(1);
  });
});
