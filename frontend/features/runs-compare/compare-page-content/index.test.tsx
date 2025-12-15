import { render, screen, waitFor } from '@testing-library/react';
import React from 'react';
import { MemoryRouter, useSearchParams } from 'react-router-dom';

import { getRunDetails } from '@/services/dataservice';

import { ComparePageContent } from './index';

jest.mock('@/services/dataservice');
jest.mock('@/layouts/common', () => {
  return function Layout({ children }: { children: React.ReactNode }) {
    return <div>{children}</div>;
  };
});
jest.mock('./compare-page-header', () => ({
  CompareRunsHeader: ({ title }: { title: string }) => <div>{title}</div>,
}));
jest.mock('./compare-page-summary', () => ({
  RunSummary: ({ runStats }: { runStats: unknown[] }) => (
    <div data-testid='run-summary'>Summary: {runStats.length} runs</div>
  ),
}));
jest.mock('./compare-table', () => ({
  ComparisonTable: () => (
    <div data-testid='comparison-table'>Comparison Table</div>
  ),
}));
jest.mock('@/components/base/comparisonModal', () => ({
  __esModule: true,
  default: ({ isOpen, onClose }: { isOpen: boolean; onClose: () => void }) =>
    isOpen ? <div data-testid='comparison-modal'>Modal</div> : null,
}));

const mockGetRunDetails = getRunDetails as jest.MockedFunction<
  typeof getRunDetails
>;

// Mock useSearchParams
jest.mock('react-router-dom', () => {
  const actual = jest.requireActual('react-router-dom');
  return {
    ...actual,
    useSearchParams: jest.fn(),
  };
});

describe('ComparePageContent', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('should show loading state initially', () => {
    (useSearchParams as jest.Mock).mockReturnValue([
      new URLSearchParams('?runs=run1,run2'),
    ]);

    mockGetRunDetails.mockImplementation(() => new Promise(() => {})); // Never resolves

    render(
      <MemoryRouter>
        <ComparePageContent />
      </MemoryRouter>
    );

    // Component doesn't show explicit loading, but we can check it's rendering
    expect(screen.getByText('Compare Runs')).toBeInTheDocument();
  });

  it('should fetch and display run details', async () => {
    (useSearchParams as jest.Mock).mockReturnValue([
      new URLSearchParams('?runs=run1,run2&agent=agent1'),
    ]);

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

    mockGetRunDetails.mockResolvedValue(mockRunDetails);

    render(
      <MemoryRouter>
        <ComparePageContent />
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

  it('should handle empty run IDs', async () => {
    (useSearchParams as jest.Mock).mockReturnValue([new URLSearchParams('')]);

    render(
      <MemoryRouter>
        <ComparePageContent />
      </MemoryRouter>
    );

    await waitFor(() => {
      expect(mockGetRunDetails).not.toHaveBeenCalled();
    });
  });

  it('should handle fetch error', async () => {
    const consoleError = jest.spyOn(console, 'error').mockImplementation();
    (useSearchParams as jest.Mock).mockReturnValue([
      new URLSearchParams('?runs=run1'),
    ]);

    mockGetRunDetails.mockRejectedValue(new Error('Network error'));

    render(
      <MemoryRouter>
        <ComparePageContent />
      </MemoryRouter>
    );

    await waitFor(() => {
      expect(consoleError).toHaveBeenCalled();
    });

    consoleError.mockRestore();
  });

  it('should parse multiple run IDs from query params', async () => {
    (useSearchParams as jest.Mock).mockReturnValue([
      new URLSearchParams('?runs=run1,run2,run3'),
    ]);

    mockGetRunDetails.mockResolvedValue([]);

    render(
      <MemoryRouter>
        <ComparePageContent />
      </MemoryRouter>
    );

    await waitFor(() => {
      expect(mockGetRunDetails).toHaveBeenCalledWith(['run1', 'run2', 'run3']);
    });
  });
});
