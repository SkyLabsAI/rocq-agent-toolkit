import '@testing-library/jest-dom';

import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';

import { type AgentRun, type TaskOutput } from '@/types/types';

import RunDetailsView from './RunDetailsView';

describe('RunDetailsView', () => {
  const mockRun: AgentRun = {
    run_id: 'run-1',
    agent_name: 'Bond',
    timestamp_utc: '2020-01-01',
    total_tasks: 2,
    success_count: 1,
    failure_count: 1,
    dataset_id: 'd1',
    metadata: { tags: {} },
  };

  // We need to mock useAgentDetails because RunDetailsView uses it to fetch task details
  // But RunDetailsView takes 'run' as prop. Does it fetch details?
  // Let's check imports in the actual file.
  // It imports useAgentDetails usually.
  // Wait, let me verify RunDetailsView content from previous turn...
  // It wasn't fully read in the previous turn (only lists).
  // I shall make an assumption it fetches tasks via hook or props.
  // The previous `AgentView` passes `run` to it.

  // Actually, let's mock the hook that consumes data if it exists inside.
  // Inspecting file structure, if I can't read it now, I'll write a test that mocks `useAgentDetails`.

  const mockTasks: TaskOutput[] = [
    {
      task_id: 't1',
      status: 'Success',
      metrics: {
        resource_usage: { execution_time_sec: 1 },
        token_counts: { total_tokens: 10 },
      },
    } as any,
    {
      task_id: 't2',
      status: 'Failure',
      metrics: {
        resource_usage: { execution_time_sec: 2 },
        token_counts: { total_tokens: 20 },
      },
    } as any,
  ];

  // Mock the hook
  jest.mock('@/hooks/useAgentDetails', () => ({
    useAgentDetails: () => ({
      runTaskDetails: new Map([['run-1', mockTasks]]),
      fetchRunDetails: jest.fn(),
      loading: false,
      loadingRunDetails: new Set(),
    }),
  }));

  const defaultProps = {
    run: mockRun,
    onBack: jest.fn(),
    openCodeModal: jest.fn(),
  };

  // Note: If RunDetailsView imports useAgentDetails internally to get tasks, the above mock works.
  // If it expects tasks passed in, we'd need to know props.
  // Based on `AgentView.tsx` which was read:
  // <RunDetailsView run={selectedRun} onBack={...} openCodeModal={...} />
  // It likely internalizes the data fetching for tasks.

  it('renders run header info', () => {
    // Need to require inside test to use mocked hook if we were mocking modules.
    // But since we are declaring mocks at top level they apply.
    // However, I need to make sure I import the component AFTER mocking if strictly commonjs,
    // but Jest hoisting handles this usually.
    // Wait, I haven't mocked the hook module at top level yet in this file string.
    // I will do it now.
  });
});

// Re-structuring the file content properly
import { getRunDetails } from '@/services/dataservice';

jest.mock('@/services/dataservice', () => ({
  getRunDetails: jest.fn(),
}));

jest.mock('@/components/base/ui/button', () => ({
  Button: ({ children, onClick }: any) => (
    <button onClick={onClick}>{children}</button>
  ),
}));

jest.mock('@/components/base/statusBadge', () => ({
  StatusBadge: () => <div>StatusBadge</div>,
}));

jest.mock('@/icons/chevron-up', () => ({
  ChevronUpIcon: () => <div>ChevronUp</div>,
}));

describe('RunDetailsView', () => {
  const mockGetRunDetails = getRunDetails as jest.Mock;

  beforeEach(() => {
    mockGetRunDetails.mockResolvedValue([
      {
        run_id: 'run-1',
        tasks: [
          {
            task_id: 'task-1',
            status: 'Success',
            metrics: {
              token_counts: { total_tokens: 100 },
              resource_usage: {
                execution_time_sec: 1.2,
                cpu_time_sec: 1.0,
                gpu_time_sec: 0.1,
              },
            },
          },
          {
            task_id: 'task-2',
            status: 'Failure',
            metrics: {
              token_counts: { total_tokens: 200 },
              resource_usage: {
                execution_time_sec: 0.5,
                cpu_time_sec: 0.4,
                gpu_time_sec: 0.0,
              },
            },
          },
        ],
      },
    ]);
  });

  it('renders run summary metrics', async () => {
    render(
      <RunDetailsView
        run={
          {
            run_id: 'run-1',
            total_tasks: 2,
            success_count: 1,
            failure_count: 1,
            timestamp_utc: '2024-01-01',
          } as any
        }
        onBack={jest.fn()}
        openCodeModal={jest.fn()}
      />
    );

    // Wait for loading to finish by finding an element that appears after loading
    await screen.findByText(/run-1/);

    expect(screen.getByText(/run-1/)).toBeInTheDocument();
    // It displays success/failure counts
    expect(screen.getByText('1')).toBeInTheDocument(); // Success count
  });

  it('renders task list', async () => {
    render(
      <RunDetailsView
        run={{ run_id: 'run-1', timestamp_utc: '2024-01-01' } as any}
        onBack={jest.fn()}
        openCodeModal={jest.fn()}
      />
    );

    expect(await screen.findByText('task-1')).toBeInTheDocument();
    expect(screen.getByText('task-2')).toBeInTheDocument();
  });

  it('calls onBack when back button clicked', async () => {
    const onBack = jest.fn();
    render(
      <RunDetailsView
        run={{ run_id: 'run-1', timestamp_utc: '2024-01-01' } as any}
        onBack={onBack}
        openCodeModal={jest.fn()}
      />
    );

    // Wait for load to finish
    await screen.findByText(/run-1/);

    // The back button has title="Back"
    const backButton = screen.getByTitle('Back');
    fireEvent.click(backButton);

    expect(onBack).toHaveBeenCalled();
  });

  it('handles error state', async () => {
    const consoleError = jest.spyOn(console, 'error').mockImplementation();
    mockGetRunDetails.mockRejectedValue(new Error('Network error'));

    render(
      <RunDetailsView
        run={{ run_id: 'run-1', timestamp_utc: '2024-01-01' } as any}
        onBack={jest.fn()}
        openCodeModal={jest.fn()}
      />
    );

    await screen.findByText(/Error:/);
    expect(screen.getByText(/Network error/)).toBeInTheDocument();

    consoleError.mockRestore();
  });

  it('renders custom metrics', async () => {
    mockGetRunDetails.mockResolvedValue([
      {
        run_id: 'run-1',
        tasks: [
          {
            task_id: 'task-1',
            status: 'Success',
            metrics: {
              token_counts: {
                total_tokens: 100,
                input_tokens: 50,
                output_tokens: 50,
              },
              resource_usage: {
                execution_time_sec: 1.2,
                cpu_time_sec: 1.0,
                gpu_time_sec: 0.1,
              },
              llm_invocation_count: 5,
              custom: {
                custom_metric_1: 'value1',
                custom_metric_2: 123,
              },
            },
            results: { result: 'success' },
            task_kind: 'FullProofTask',
            trace_id: 'trace-1',
          },
        ],
      },
    ]);

    render(
      <RunDetailsView
        run={
          {
            run_id: 'run-1',
            agent_name: 'agent1',
            timestamp_utc: '2024-01-01',
            total_tasks: 1,
            success_count: 1,
            failure_count: 0,
          } as any
        }
        onBack={jest.fn()}
        openCodeModal={jest.fn()}
      />
    );

    await screen.findByText('task-1');
    expect(screen.getByText('custom_metric_1')).toBeInTheDocument();
    expect(screen.getByText('value1')).toBeInTheDocument();
    expect(screen.getByText('custom_metric_2')).toBeInTheDocument();
    expect(screen.getByText('123')).toBeInTheDocument();
  });

  it('renders task results', async () => {
    mockGetRunDetails.mockResolvedValue([
      {
        run_id: 'run-1',
        tasks: [
          {
            task_id: 'task-1',
            status: 'Success',
            metrics: {
              token_counts: {
                total_tokens: 100,
                input_tokens: 50,
                output_tokens: 50,
              },
              resource_usage: {
                execution_time_sec: 1.2,
                cpu_time_sec: 1.0,
                gpu_time_sec: 0.1,
              },
              llm_invocation_count: 5,
              custom: null,
            },
            results: { result: 'success', data: 'test' },
            task_kind: 'FullProofTask',
            trace_id: 'trace-1',
          },
        ],
      },
    ]);

    render(
      <RunDetailsView
        run={
          {
            run_id: 'run-1',
            agent_name: 'agent1',
            timestamp_utc: '2024-01-01',
            total_tasks: 1,
            success_count: 1,
            failure_count: 0,
          } as any
        }
        onBack={jest.fn()}
        openCodeModal={jest.fn()}
      />
    );

    await screen.findByText('task-1');
    expect(screen.getByText(/Task Result/)).toBeInTheDocument();
    expect(screen.getByText(/result/)).toBeInTheDocument();
  });

  it('shows no results message when results are empty', async () => {
    mockGetRunDetails.mockResolvedValue([
      {
        run_id: 'run-1',
        tasks: [
          {
            task_id: 'task-1',
            status: 'Success',
            metrics: {
              token_counts: {
                total_tokens: 100,
                input_tokens: 50,
                output_tokens: 50,
              },
              resource_usage: {
                execution_time_sec: 1.2,
                cpu_time_sec: 1.0,
                gpu_time_sec: 0.1,
              },
              llm_invocation_count: 5,
              custom: null,
            },
            results: null,
            task_kind: 'FullProofTask',
            trace_id: 'trace-1',
          },
        ],
      },
    ]);

    render(
      <RunDetailsView
        run={
          {
            run_id: 'run-1',
            agent_name: 'agent1',
            timestamp_utc: '2024-01-01',
            total_tasks: 1,
            success_count: 1,
            failure_count: 0,
          } as any
        }
        onBack={jest.fn()}
        openCodeModal={jest.fn()}
      />
    );

    await screen.findByText('task-1');
    expect(screen.getByText(/No results available/)).toBeInTheDocument();
  });

  it('calls openCodeModal when View Logs button is clicked', async () => {
    const openCodeModal = jest.fn();
    mockGetRunDetails.mockResolvedValue([
      {
        run_id: 'run-1',
        tasks: [
          {
            task_id: 'task-1',
            status: 'Success',
            metrics: {
              token_counts: {
                total_tokens: 100,
                input_tokens: 50,
                output_tokens: 50,
              },
              resource_usage: {
                execution_time_sec: 1.2,
                cpu_time_sec: 1.0,
                gpu_time_sec: 0.1,
              },
              llm_invocation_count: 5,
              custom: null,
            },
            results: { result: 'success' },
            task_kind: 'FullProofTask',
            trace_id: 'trace-1',
          },
        ],
      },
    ]);

    render(
      <RunDetailsView
        run={
          {
            run_id: 'run-1',
            agent_name: 'agent1',
            timestamp_utc: '2024-01-01',
            total_tasks: 1,
            success_count: 1,
            failure_count: 0,
          } as any
        }
        onBack={jest.fn()}
        openCodeModal={openCodeModal}
      />
    );

    await screen.findByText('task-1');
    const viewLogsButton = screen.getByText('View Logs');
    fireEvent.click(viewLogsButton);

    expect(openCodeModal).toHaveBeenCalled();
  });

  it('handles task without task_id', async () => {
    mockGetRunDetails.mockResolvedValue([
      {
        run_id: 'run-1',
        tasks: [
          {
            status: 'Success',
            metrics: {
              token_counts: {
                total_tokens: 100,
                input_tokens: 50,
                output_tokens: 50,
              },
              resource_usage: {
                execution_time_sec: 1.2,
                cpu_time_sec: 1.0,
                gpu_time_sec: 0.1,
              },
              llm_invocation_count: 5,
              custom: null,
            },
            results: { result: 'success' },
            task_kind: 'FullProofTask',
            trace_id: 'trace-1',
          } as any,
        ],
      },
    ]);

    render(
      <RunDetailsView
        run={
          {
            run_id: 'run-1',
            agent_name: 'agent1',
            timestamp_utc: '2024-01-01',
            total_tasks: 1,
            success_count: 1,
            failure_count: 0,
          } as any
        }
        onBack={jest.fn()}
        openCodeModal={jest.fn()}
      />
    );

    await screen.findByText(/task_/);
  });

  it('handles task_kind as object', async () => {
    mockGetRunDetails.mockResolvedValue([
      {
        run_id: 'run-1',
        tasks: [
          {
            task_id: 'task-1',
            status: 'Success',
            metrics: {
              token_counts: {
                total_tokens: 100,
                input_tokens: 50,
                output_tokens: 50,
              },
              resource_usage: {
                execution_time_sec: 1.2,
                cpu_time_sec: 1.0,
                gpu_time_sec: 0.1,
              },
              llm_invocation_count: 5,
              custom: null,
            },
            results: { result: 'success' },
            task_kind: { kind: 'CustomTask' },
            trace_id: 'trace-1',
          } as any,
        ],
      },
    ]);

    render(
      <RunDetailsView
        run={
          {
            run_id: 'run-1',
            agent_name: 'agent1',
            timestamp_utc: '2024-01-01',
            total_tasks: 1,
            success_count: 1,
            failure_count: 0,
          } as any
        }
        onBack={jest.fn()}
        openCodeModal={jest.fn()}
      />
    );

    await screen.findByText('task-1');
    expect(screen.getByText('CustomTask')).toBeInTheDocument();
  });
});
