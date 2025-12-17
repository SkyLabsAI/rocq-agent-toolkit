import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';

import { type RunTaskCell } from '@/features/runs-compare';

import { TaskHeader } from './index';

jest.mock('@/components/base/statusBadge', () => ({
  StatusBadge: ({ status }: { status: string }) => (
    <div data-testid={`status-${status}`}>{status}</div>
  ),
}));

describe('TaskHeader', () => {
  const mockDetails: RunTaskCell[] = [
    {
      run: {
        run_id: 'run1',
        agent_name: 'agent1',
        total_tasks: 1,
        tasks: [],
      },
      task: {
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
    },
  ];

  it('should render task ID', () => {
    render(
      <TaskHeader
        id='task1'
        details={mockDetails}
        onOpenModal={jest.fn()}
        onClick={jest.fn()}
        isExpanded={false}
      />
    );

    expect(screen.getByText(/Task ID: task1/)).toBeInTheDocument();
  });

  it('should render status badges', () => {
    render(
      <TaskHeader
        id='task1'
        details={mockDetails}
        onOpenModal={jest.fn()}
        onClick={jest.fn()}
        isExpanded={false}
      />
    );

    expect(screen.getByTestId('status-Success')).toBeInTheDocument();
  });

  it('should call onOpenModal when compare button is clicked', () => {
    const handleOpenModal = jest.fn();
    render(
      <TaskHeader
        id='task1'
        details={mockDetails}
        onOpenModal={handleOpenModal}
        onClick={jest.fn()}
        isExpanded={false}
      />
    );

    fireEvent.click(screen.getByText('Compare Details'));

    expect(handleOpenModal).toHaveBeenCalledWith('task1');
  });

  it('should call onClick when header is clicked', () => {
    const handleClick = jest.fn();
    render(
      <TaskHeader
        id='task1'
        details={mockDetails}
        onOpenModal={jest.fn()}
        onClick={handleClick}
        isExpanded={false}
      />
    );

    const header = screen.getByText(/Task ID: task1/).closest('div');
    if (header) {
      fireEvent.click(header);
      expect(handleClick).toHaveBeenCalled();
    }
  });

  it('should show expanded state', () => {
    render(
      <TaskHeader
        id='task1'
        details={mockDetails}
        onOpenModal={jest.fn()}
        onClick={jest.fn()}
        isExpanded={true}
      />
    );

    expect(screen.getByText(/Task ID: task1/)).toBeInTheDocument();
  });

  it('should handle details without tasks', () => {
    const detailsWithoutTask: RunTaskCell[] = [
      {
        run: {
          run_id: 'run1',
          agent_name: 'agent1',
          total_tasks: 1,
          tasks: [],
        },
      },
    ];

    render(
      <TaskHeader
        id='task1'
        details={detailsWithoutTask}
        onOpenModal={jest.fn()}
        onClick={jest.fn()}
        isExpanded={false}
      />
    );

    expect(screen.getByTestId('status-Failure')).toBeInTheDocument();
  });
});
