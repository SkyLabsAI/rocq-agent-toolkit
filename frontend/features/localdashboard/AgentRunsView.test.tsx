import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';

import { useSelectedRun } from '@/contexts/selected-run-context';

import AgentRunsView, {isLatestRun} from './agent-runs-view';

jest.mock('@/contexts/selected-run-context');
jest.mock('@/components/run-row', () => ({
  __esModule: true,
  default: ({
    run,
    isLatest,
    isSelected,
    isPinned,
    onToggleExpansion,
    onToggleSelection,
    onPin,
  }: {
    run: { run_id: string };
    isLatest: boolean;
    isSelected: boolean;
    isPinned: boolean;
    onToggleExpansion: () => void;
    onToggleSelection: () => void;
    onPin: () => void;
  }) => (
    <div data-testid={`run-row-${run.run_id}`}>
      {run.run_id} - Latest: {isLatest ? 'yes' : 'no'} - Selected:{' '}
      {isSelected ? 'yes' : 'no'} - Pinned: {isPinned ? 'yes' : 'no'}
      <button onClick={onToggleExpansion}>Expand</button>
      <button onClick={onToggleSelection}>Toggle</button>
      <button onClick={onPin}>Pin</button>
    </div>
  ),
}));
jest.mock('@/components/sticky-compare-bar', () => ({
  __esModule: true,
  default: ({
    selectedItems,
    onClearSelection,
    onCompareSelected,
  }: {
    selectedItems: string[];
    onClearSelection: () => void;
    onCompareSelected: () => void;
  }) => (
    <div data-testid='sticky-compare-bar'>
      Selected: {selectedItems.length}
      <button onClick={onClearSelection}>Clear</button>
      <button onClick={onCompareSelected}>Compare</button>
    </div>
  ),
}));

const mockUseSelectedRun = useSelectedRun as jest.MockedFunction<
  typeof useSelectedRun
>;

// Mock localStorage
const localStorageMock = (() => {
  let store: Record<string, string> = {};
  return {
    getItem: (key: string) => store[key] || null,
    setItem: (key: string, value: string) => {
      store[key] = value;
    },
    clear: () => {
      store = {};
    },
  };
})();

Object.defineProperty(window, 'localStorage', {
  value: localStorageMock,
});

describe('AgentRunsView', () => {
  const mockRuns = [
    {
      run_id: 'run1',
      agent_name: 'agent1',
      timestamp_utc: '2024-01-02T00:00:00Z',
      total_tasks: 10,
      success_count: 8,
      failure_count: 2,
      dataset_id: 'bench1',
      metadata: { tags: {} },
    },
    {
      run_id: 'run2',
      agent_name: 'agent1',
      timestamp_utc: '2024-01-01T00:00:00Z',
      total_tasks: 8,
      success_count: 6,
      failure_count: 2,
      dataset_id: 'bench1',
      metadata: { tags: {} },
    },
  ];

  beforeEach(() => {
    jest.clearAllMocks();
    localStorageMock.clear();

    mockUseSelectedRun.mockReturnValue({
      selectedRun: null,
      setSelectedRun: jest.fn(),
    });
  });

  it('should render runs', () => {
    render(
      <AgentRunsView
        runDetails={mockRuns}
        agentName='agent1'
        selectedRuns={[]}
        toggleRunSelection={jest.fn()}
        clearSelectedRuns={jest.fn()}
        compareSelected={jest.fn()}
      />
    );

    expect(screen.getByTestId('run-row-run1')).toBeInTheDocument();
    expect(screen.getByTestId('run-row-run2')).toBeInTheDocument();
  });

  it('should mark latest run correctly', () => {
    render(
      <AgentRunsView
        runDetails={mockRuns}
        agentName='agent1'
        selectedRuns={[]}
        toggleRunSelection={jest.fn()}
        clearSelectedRuns={jest.fn()}
        compareSelected={jest.fn()}
      />
    );

    const run1 = screen.getByTestId('run-row-run1');
    expect(run1).toHaveTextContent('Latest: yes');
  });

  it('should show selected runs', () => {
    render(
      <AgentRunsView
        runDetails={mockRuns}
        agentName='agent1'
        selectedRuns={['run1']}
        toggleRunSelection={jest.fn()}
        clearSelectedRuns={jest.fn()}
        compareSelected={jest.fn()}
      />
    );

    const run1 = screen.getByTestId('run-row-run1');
    expect(run1).toHaveTextContent('Selected: yes');
  });

  it('should render sticky compare bar when runs are selected', () => {
    render(
      <AgentRunsView
        runDetails={mockRuns}
        agentName='agent1'
        selectedRuns={['run1', 'run2']}
        toggleRunSelection={jest.fn()}
        clearSelectedRuns={jest.fn()}
        compareSelected={jest.fn()}
      />
    );

    expect(screen.getByTestId('sticky-compare-bar')).toBeInTheDocument();
    expect(screen.getByText('Selected: 2')).toBeInTheDocument();
  });
});

describe('isLatestRun', () => {
  it('should return true for latest run', () => {
    const runs = [
      {
        run_id: 'run1',
        agent_name: 'agent1',
        timestamp_utc: '2024-01-02',
        total_tasks: 10,
        success_count: 8,
        failure_count: 2,
        dataset_id: 'bench1',
        metadata: { tags: {} },
      },
      {
        run_id: 'run2',
        agent_name: 'agent1',
        timestamp_utc: '2024-01-01',
        total_tasks: 8,
        success_count: 6,
        failure_count: 2,
        dataset_id: 'bench1',
        metadata: { tags: {} },
      },
    ];

    expect(isLatestRun(runs[0], runs)).toBe(true);
    expect(isLatestRun(runs[1], runs)).toBe(false);
  });

  it('should return false for empty runs array', () => {
    const run = {
      run_id: 'run1',
      agent_name: 'agent1',
      timestamp_utc: '2024-01-01',
      total_tasks: 10,
      success_count: 8,
      failure_count: 2,
      dataset_id: 'bench1',
      metadata: { tags: {} },
    };

    expect(isLatestRun(run, [])).toBe(false);
  });
});
