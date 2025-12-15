import { fireEvent, render, screen } from '@testing-library/react';
import { within } from '@testing-library/react';
import React from 'react';

import { type RunDetailsResponse } from '@/types/types';

import { ComparisonTable } from './index';

jest.mock('./compare-table-header', () => ({
  TaskComparisonHeaderTop: ({ runs }: { runs: unknown[] }) => (
    <div data-testid='task-comparison-header'>Header: {runs.length} runs</div>
  ),
}));
jest.mock('./compare-table-header/task-header', () => ({
  TaskHeader: ({
    id,
    onOpenModal,
    onClick,
  }: {
    id: string;
    onOpenModal: (id: string) => void;
    onClick: () => void;
  }) => (
    <div data-testid={`task-header-${id}`}>
      <button onClick={() => onOpenModal(id)}>Open Modal</button>
      <button onClick={onClick}>Toggle</button>
    </div>
  ),
}));
jest.mock('./compare-table-header/task-details', () => ({
  TaskDetailsTable: ({
    id,
    taskRowData,
  }: {
    id: string;
    taskRowData: { taskId: string };
  }) => (
    <div data-testid={`task-details-${id}`}>Task: {taskRowData.taskId}</div>
  ),
}));

describe('ComparisonTable', () => {
  const mockRuns: RunDetailsResponse[] = [
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
  ];

  const mockTaskMap = {
    task1: [
      {
        run: mockRuns[0],
        task: mockRuns[0].tasks[0],
      },
    ],
  };

  const mockTaskRowData = [
    {
      taskId: 'task1',
      cells: [
        {
          runId: 'run1',
          runName: 'agent1',
          task: mockRuns[0].tasks[0],
        },
      ],
    },
  ];

  it('should render comparison table', () => {
    render(
      <ComparisonTable
        runs={mockRuns}
        taskMap={mockTaskMap}
        allTaskIds={['task1']}
        selectedTaskId={null}
        onSelectTask={jest.fn()}
        onOpenModal={jest.fn()}
        showTasks={true}
        taskRowData={mockTaskRowData}
        onToggleShowTasks={jest.fn()}
      />
    );

    expect(screen.getByTestId('task-comparison-header')).toBeInTheDocument();
    expect(screen.getByTestId('task-header-task1')).toBeInTheDocument();
  });

  it('should call onOpenModal when task header button is clicked', () => {
    const handleOpenModal = jest.fn();
    render(
      <ComparisonTable
        runs={mockRuns}
        taskMap={mockTaskMap}
        allTaskIds={['task1']}
        selectedTaskId={null}
        onSelectTask={jest.fn()}
        onOpenModal={handleOpenModal}
        showTasks={true}
        taskRowData={mockTaskRowData}
        onToggleShowTasks={jest.fn()}
      />
    );

    fireEvent.click(screen.getByText('Open Modal'));

    expect(handleOpenModal).toHaveBeenCalledWith('task1');
  });

  it('should render task details when expanded', () => {
    render(
      <ComparisonTable
        runs={mockRuns}
        taskMap={mockTaskMap}
        allTaskIds={['task1']}
        selectedTaskId={null}
        onSelectTask={jest.fn()}
        onOpenModal={jest.fn()}
        showTasks={true}
        taskRowData={mockTaskRowData}
        onToggleShowTasks={jest.fn()}
      />
    );

    // Assert details container exists and contains the task name
    const details = screen.getByTestId('task-details-undefined');
    expect(details).toBeInTheDocument();
    expect(details).toHaveTextContent(/task1/);
  });
});
