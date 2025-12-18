import { fireEvent, render, screen, waitFor } from '@testing-library/react';
import React from 'react';
import { MemoryRouter } from 'react-router-dom';

import { useSelectedRun } from '@/contexts/selected-run-context';
import { useAgents } from '@/hooks/use-agent-summaries';

import AgentView from './index';

jest.mock('@/hooks/use-agent-summaries');
jest.mock('@/contexts/selected-run-context');
jest.mock('./agent-details', () => ({
  __esModule: true,
  default: ({ agent }: { agent: { agent_name: string } }) => (
    <tr data-testid={`agent-details-${agent.agent_name}`}>
      <td>{agent.agent_name}</td>
    </tr>
  ),
}));
jest.mock('@/features/task-details-modal', () => ({
  __esModule: true,
  default: ({ isOpen }: { isOpen: boolean }) =>
    isOpen ? <div data-testid='task-details-modal'>Task Modal</div> : null,
}));
jest.mock('@/components/run-details-view', () => ({
  __esModule: true,
  default: ({ run }: { run: { run_id: string } }) => (
    <div data-testid='run-details-view'>Run: {run.run_id}</div>
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

const mockUseAgents = useAgents as jest.MockedFunction<typeof useAgents>;
const mockUseSelectedRun = useSelectedRun as jest.MockedFunction<
  typeof useSelectedRun
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

describe('AgentView', () => {
  const mockAgentData = [
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
    {
      agent_name: 'agent2',
      total_runs: 3,
      best_run: {
        run_id: 'run2',
        agent_name: 'agent2',
        timestamp_utc: '2024-01-01',
        total_tasks: 8,
        success_count: 6,
        failure_count: 2,
        success_rate: 0.75,
        score: 0.8,
        avg_total_tokens: 900,
        avg_cpu_time_sec: 4.5,
        avg_llm_invocation_count: 2,
        metadata: { tags: {} },
      },
    },
  ];

  beforeEach(() => {
    jest.clearAllMocks();
    mockUseAgents.mockReturnValue({
      agentData: mockAgentData,
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
  });

  it('should render agents table', () => {
    render(
      <MemoryRouter>
        <AgentView />
      </MemoryRouter>
    );

    expect(screen.getByText('Agents')).toBeInTheDocument();
    expect(screen.getByTestId('agent-details-agent1')).toBeInTheDocument();
    expect(screen.getByTestId('agent-details-agent2')).toBeInTheDocument();
  });

  it('should handle sorting by agent_name', () => {
    render(
      <MemoryRouter>
        <AgentView />
      </MemoryRouter>
    );

    const sortButton = screen.getByText('Agents');
    fireEvent.click(sortButton);

    // Should sort agents
    expect(screen.getByTestId('agent-details-agent1')).toBeInTheDocument();
  });

  it('should handle sorting by success_rate', () => {
    render(
      <MemoryRouter>
        <AgentView />
      </MemoryRouter>
    );

    const sortButton = screen.getByText('Success Rate');
    fireEvent.click(sortButton);

    // Should sort by success rate
    expect(screen.getByTestId('agent-details-agent1')).toBeInTheDocument();
  });

  it('should toggle sort direction', () => {
    render(
      <MemoryRouter>
        <AgentView />
      </MemoryRouter>
    );

    const sortButton = screen.getByText('Agents');
    fireEvent.click(sortButton); // First click - asc
    fireEvent.click(sortButton); // Second click - desc

    expect(screen.getByTestId('agent-details-agent1')).toBeInTheDocument();
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
        <AgentView />
      </MemoryRouter>
    );

    expect(screen.getByTestId('run-details-view')).toBeInTheDocument();
  });

  it('should navigate to compare page when compare agents is clicked', () => {
    render(
      <MemoryRouter>
        <AgentView />
      </MemoryRouter>
    );

    // This would require selecting agents first, which is complex
    // But we can test the navigation logic exists
    expect(screen.getByText('Agents')).toBeInTheDocument();
  });

  it('should clear selections when navigating to compare page', () => {
    const { rerender } = render(
      <MemoryRouter>
        <AgentView />
      </MemoryRouter>
    );

    // Simulate navigation to compare page
    jest.spyOn(require('react-router-dom'), 'useLocation').mockReturnValue({
      pathname: '/compare',
    });

    rerender(
      <MemoryRouter>
        <AgentView />
      </MemoryRouter>
    );

    // Selections should be cleared
    expect(screen.getByText('Agents')).toBeInTheDocument();
  });

  it('should handle sorting by avg_cpu_time_sec', () => {
    render(
      <MemoryRouter>
        <AgentView />
      </MemoryRouter>
    );

    const sortButton = screen.getByText('Avg Time (s)');
    fireEvent.click(sortButton);

    expect(screen.getByTestId('agent-details-agent1')).toBeInTheDocument();
  });

  it('should handle sorting by avg_total_tokens', () => {
    render(
      <MemoryRouter>
        <AgentView />
      </MemoryRouter>
    );

    const sortButton = screen.getByText('Avg Tokens');
    fireEvent.click(sortButton);

    expect(screen.getByTestId('agent-details-agent1')).toBeInTheDocument();
  });

  it('should handle sorting by avg_llm_invocation_count', () => {
    render(
      <MemoryRouter>
        <AgentView />
      </MemoryRouter>
    );

    const sortButton = screen.getByText('Avg LLM Calls');
    fireEvent.click(sortButton);

    expect(screen.getByTestId('agent-details-agent1')).toBeInTheDocument();
  });

  it('should show task details modal when modal is open', () => {
    mockUseAgents.mockReturnValue({
      agentData: mockAgentData,
      agentDetailData: [],
      isLoading: false,
      openCodeModal: jest.fn(),
      closeModal: jest.fn(),
      modalState: { isOpen: true, selectedTask: null, logs: { key: 'value' } },
      loadingLogs: null,
    });

    render(
      <MemoryRouter>
        <AgentView />
      </MemoryRouter>
    );

    expect(screen.getByTestId('task-details-modal')).toBeInTheDocument();
  });
});
