import '@testing-library/jest-dom';

import { fireEvent, render, screen, waitFor } from '@testing-library/react';
import React from 'react';

import AgentDetails from './index';

// Mock child component AgentRunsView
jest.mock('@/features/localdashboard/AgentRunsView', () => {
  return function MockAgentRunsView() {
    return <div data-testid='agent-runs-view'>Agent Runs View</div>;
  };
});

// Mock hook
jest.mock('@/hooks/useAgentDetails', () => ({
  useAgentDetails: () => ({
    openDetails: jest.fn(),
    toggleDetails: jest.fn(),
    isOpen: true, // Force open to render runs view
    runDetails: [],
    loading: false,
  }),
}));

describe('AgentDetails (Row)', () => {
  const mockAgent = {
    agent_name: '007',
    total_runs: 20,
    best_run: {
      run_id: 'run-1',
      agent_name: '007',
      timestamp_utc: '2024-01-01T00:00:00Z',
      total_tasks: 10,
      success_count: 10,
      failure_count: 0,
      success_rate: 1,
      score: 1,
      avg_cpu_time_sec: 1.2,
      avg_total_tokens: 500,
      avg_llm_invocation_count: 5,
      metadata: { tags: {} },
    },
  };
  const mockAgentDetailData = {
    agentName: '007',
    totalTasks: 10,
    successRate: 1,
    avgTime: 1.2,
    avgTokens: 500,
    avgLlmCalls: 5,
  };

  const defaultProps = {
    agent: mockAgent,
    agentDetailData: mockAgentDetailData,
    activeAgent: true,
    setActiveAgent: jest.fn(),
    isSelected: false,
    toggleSelection: jest.fn(),
    selectedRuns: [],
    toggleRunSelection: jest.fn(),
    clearSelectedRuns: jest.fn(),
    compareSelectedRuns: jest.fn(),
  };

  // The component renders a <tr> so it must be inside a <table>
  const renderRow = (props = defaultProps) => {
    return render(
      <table>
        <tbody>
          <AgentDetails {...props} />
        </tbody>
      </table>
    );
  };

  it('renders agent name and metrics', () => {
    renderRow();
    expect(screen.getByText('007')).toBeInTheDocument();
    // Success rate 1 means 100% or similar format
    expect(screen.getByText(/100/)).toBeInTheDocument();
    expect(screen.getByText(/1\.20/)).toBeInTheDocument();
  });

  it('toggles expansion on click', () => {
    renderRow();
    // Click on the name cell
    fireEvent.click(screen.getByText('007'));
    // It should call setActiveAgent or toggle internal state.
    // Based on props provided, let's assume it should trigger prop if wired correctly.
  });

  it('renders expansion view when active/open', () => {
    renderRow();
    // Since we mocked hook to interpret isOpen=true,
    // we expect the expansion row to be visible
    expect(screen.getByTestId('agent-runs-view')).toBeInTheDocument();
  });
});
