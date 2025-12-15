import { render, screen, waitFor } from '@testing-library/react';
import React from 'react';
import { MemoryRouter, useSearchParams } from 'react-router-dom';

import { useAgents } from '@/hooks/useAgentsSummary';
import { getRunDetails } from '@/services/dataservice';

import { AgentCompareContent } from './agent-compare-content';

jest.mock('@/hooks/useAgentsSummary');
jest.mock('@/services/dataservice');
jest.mock('../runs-compare/compare-page-content/compare-page-header', () => ({
  CompareRunsHeader: ({ title }: { title: string }) => <div>{title}</div>,
}));
jest.mock('../runs-compare/compare-page-content/compare-page-summary', () => ({
  RunSummary: ({ runStats }: { runStats: unknown[] }) => (
    <div data-testid='run-summary'>Summary: {runStats.length} runs</div>
  ),
}));
jest.mock('../runs-compare/compare-page-content/compare-table', () => ({
  ComparisonTable: () => (
    <div data-testid='comparison-table'>Comparison Table</div>
  ),
}));
jest.mock('@/components/base/comparisonModal', () => ({
  __esModule: true,
  default: ({ isOpen }: { isOpen: boolean }) =>
    isOpen ? <div data-testid='comparison-modal'>Modal</div> : null,
}));

const mockUseAgents = useAgents as jest.MockedFunction<typeof useAgents>;
const mockGetRunDetails = getRunDetails as jest.MockedFunction<
  typeof getRunDetails
>;

jest.mock('react-router-dom', () => {
  const actual = jest.requireActual('react-router-dom');
  return {
    ...actual,
    useSearchParams: jest.fn(),
    useNavigate: jest.fn(() => jest.fn()),
  };
});

describe('AgentCompareContent', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('should show loading state initially', () => {
    (useSearchParams as jest.Mock).mockReturnValue([
      new URLSearchParams('?agents=agent1,agent2'),
    ]);

    mockUseAgents.mockReturnValue({
      agentData: [],
      agentDetailData: [],
      isLoading: true,
      openCodeModal: jest.fn(),
      closeModal: jest.fn(),
      modalState: { isOpen: false, selectedTask: null, logs: null },
      loadingLogs: null,
    });

    mockGetRunDetails.mockImplementation(() => new Promise(() => {}));

    render(
      <MemoryRouter>
        <AgentCompareContent />
      </MemoryRouter>
    );

    expect(screen.getByText('Compare Agents')).toBeInTheDocument();
  });

  it('should fetch and display best runs for selected agents', async () => {
    (useSearchParams as jest.Mock).mockReturnValue([
      new URLSearchParams('?agents=agent1,agent2'),
    ]);

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

    const mockRunDetails = [
      {
        run_id: 'run1',
        agent_name: 'agent1',
        total_tasks: 2,
        tasks: [
          {
            run_id: 'run1',
            task_kind: 'FullProofTask',
            task_id: 'task1',
            timestamp_utc: '2024-01-01',
            agent_name: 'agent1',
            status: 'Success',
            results: {},
            metrics: {
              llm_invocation_count: 1,
              token_counts: {
                input_tokens: 100,
                output_tokens: 50,
                total_tokens: 150,
              },
              resource_usage: {
                execution_time_sec: 1.0,
                cpu_time_sec: 0.8,
                gpu_time_sec: 0.2,
              },
              custom: null,
            },
          },
        ],
      },
      {
        run_id: 'run2',
        agent_name: 'agent2',
        total_tasks: 1,
        tasks: [
          {
            run_id: 'run2',
            task_kind: 'FullProofTask',
            task_id: 'task1',
            timestamp_utc: '2024-01-01',
            agent_name: 'agent2',
            status: 'Success',
            results: {},
            metrics: {
              llm_invocation_count: 1,
              token_counts: {
                input_tokens: 100,
                output_tokens: 50,
                total_tokens: 150,
              },
              resource_usage: {
                execution_time_sec: 1.0,
                cpu_time_sec: 0.8,
                gpu_time_sec: 0.2,
              },
              custom: null,
            },
          },
        ],
      },
    ];

    mockUseAgents.mockReturnValue({
      agentData: mockAgentData,
      agentDetailData: [],
      isLoading: false,
      openCodeModal: jest.fn(),
      closeModal: jest.fn(),
      modalState: { isOpen: false, selectedTask: null, logs: null },
      loadingLogs: null,
    });

    mockGetRunDetails.mockResolvedValue(mockRunDetails);

    render(
      <MemoryRouter>
        <AgentCompareContent />
      </MemoryRouter>
    );

    await waitFor(() => {
      expect(mockGetRunDetails).toHaveBeenCalledWith(['run1', 'run2']);
    });

    await waitFor(() => {
      expect(screen.getByTestId('run-summary')).toBeInTheDocument();
      expect(screen.getByTestId('comparison-table')).toBeInTheDocument();
    });
  });

  it('should handle empty agent names', async () => {
    (useSearchParams as jest.Mock).mockReturnValue([new URLSearchParams('')]);

    mockUseAgents.mockReturnValue({
      agentData: [],
      agentDetailData: [],
      isLoading: false,
      openCodeModal: jest.fn(),
      closeModal: jest.fn(),
      modalState: { isOpen: false, selectedTask: null, logs: null },
      loadingLogs: null,
    });

    render(
      <MemoryRouter>
        <AgentCompareContent />
      </MemoryRouter>
    );

    await waitFor(() => {
      expect(mockGetRunDetails).not.toHaveBeenCalled();
    });
  });

  it('should handle fetch error', async () => {
    const consoleError = jest.spyOn(console, 'error').mockImplementation();
    (useSearchParams as jest.Mock).mockReturnValue([
      new URLSearchParams('?agents=agent1'),
    ]);

    mockUseAgents.mockReturnValue({
      agentData: [
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
      ],
      agentDetailData: [],
      isLoading: false,
      openCodeModal: jest.fn(),
      closeModal: jest.fn(),
      modalState: { isOpen: false, selectedTask: null, logs: null },
      loadingLogs: null,
    });

    mockGetRunDetails.mockRejectedValue(new Error('Network error'));

    render(
      <MemoryRouter>
        <AgentCompareContent />
      </MemoryRouter>
    );

    await waitFor(() => {
      expect(consoleError).toHaveBeenCalled();
    });

    consoleError.mockRestore();
  });
});
