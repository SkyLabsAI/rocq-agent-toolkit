import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';

import type { TaskOutput } from '@/types/types';

import TasksTable from './tasks-table';

describe('TasksTable', () => {
  const mockTasks: TaskOutput[] = [
    {
      run_id: 'run_1',
      task_kind: 'FullProofTask',
      task_id: 'task_001',
      trace_id: 'trace_001',
      timestamp_utc: '2024-01-01T00:00:00Z',
      agent_name: 'test-agent',
      status: 'Success',
      results: null,
      metrics: {
        llm_invocation_count: 5,
        token_counts: {
          input_tokens: 100,
          output_tokens: 50,
          total_tokens: 150,
        },
        resource_usage: {
          execution_time_sec: 1.5,
          cpu_time_sec: 1.2,
          gpu_time_sec: 0.3,
        },
        custom: null,
      },
    },
    {
      run_id: 'run_1',
      task_kind: 'FullProofTask',
      task_id: 'task_002',
      trace_id: 'trace_002',
      timestamp_utc: '2024-01-01T00:00:00Z',
      agent_name: 'test-agent',
      status: 'Failure',
      results: null,
      metrics: {
        llm_invocation_count: 3,
        token_counts: {
          input_tokens: 80,
          output_tokens: 40,
          total_tokens: 120,
        },
        resource_usage: {
          execution_time_sec: 2.0,
          cpu_time_sec: 1.8,
          gpu_time_sec: 0.2,
        },
        custom: null,
      },
    },
  ];

  const mockOnTaskClick = jest.fn();

  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('renders the table with tasks', () => {
    render(<TasksTable tasks={mockTasks} onTaskClick={mockOnTaskClick} />);

    expect(screen.getByText('task_001')).toBeInTheDocument();
    expect(screen.getByText('task_002')).toBeInTheDocument();
  });

  it('shows the correct count of tasks', () => {
    render(<TasksTable tasks={mockTasks} onTaskClick={mockOnTaskClick} />);

    expect(screen.getByText('Showing 2 of 2 tasks')).toBeInTheDocument();
  });

  it('filters tasks by task ID', () => {
    render(<TasksTable tasks={mockTasks} onTaskClick={mockOnTaskClick} />);

    const taskIdInput = screen.getByPlaceholderText('Search task ID...');
    fireEvent.change(taskIdInput, { target: { value: '001' } });

    expect(screen.getByText('task_001')).toBeInTheDocument();
    expect(screen.queryByText('task_002')).not.toBeInTheDocument();
    expect(screen.getByText('Showing 1 of 2 tasks')).toBeInTheDocument();
  });

  it('filters tasks by status', () => {
    render(<TasksTable tasks={mockTasks} onTaskClick={mockOnTaskClick} />);

    const statusSelect = screen.getByLabelText('Filter by Status');
    fireEvent.change(statusSelect, { target: { value: 'Success' } });

    expect(screen.getByText('task_001')).toBeInTheDocument();
    expect(screen.queryByText('task_002')).not.toBeInTheDocument();
    expect(screen.getByText('Showing 1 of 2 tasks')).toBeInTheDocument();
  });

  it('shows no tasks message when filters match nothing', () => {
    render(<TasksTable tasks={mockTasks} onTaskClick={mockOnTaskClick} />);

    const taskIdInput = screen.getByPlaceholderText('Search task ID...');
    fireEvent.change(taskIdInput, { target: { value: 'nonexistent' } });

    expect(
      screen.getByText('No tasks found matching your filters')
    ).toBeInTheDocument();
    expect(screen.getByText('Showing 0 of 2 tasks')).toBeInTheDocument();
  });

  it('calls onTaskClick when a task row is clicked', () => {
    render(<TasksTable tasks={mockTasks} onTaskClick={mockOnTaskClick} />);

    const firstTaskRow = screen.getByText('task_001').closest('tr');
    if (firstTaskRow) {
      fireEvent.click(firstTaskRow);
    }

    expect(mockOnTaskClick).toHaveBeenCalledTimes(1);
    expect(mockOnTaskClick).toHaveBeenCalledWith(mockTasks[0]);
  });

  it('handles multiple filters simultaneously', () => {
    render(<TasksTable tasks={mockTasks} onTaskClick={mockOnTaskClick} />);

    const taskIdInput = screen.getByPlaceholderText('Search task ID...');
    const statusSelect = screen.getByLabelText('Filter by Status');

    fireEvent.change(taskIdInput, { target: { value: '00' } });
    fireEvent.change(statusSelect, { target: { value: 'Failure' } });

    expect(screen.queryByText('task_001')).not.toBeInTheDocument();
    expect(screen.getByText('task_002')).toBeInTheDocument();
    expect(screen.getByText('Showing 1 of 2 tasks')).toBeInTheDocument();
  });

  it('handles empty tasks array', () => {
    render(<TasksTable tasks={[]} onTaskClick={mockOnTaskClick} />);

    expect(
      screen.getByText('No tasks found matching your filters')
    ).toBeInTheDocument();
    expect(screen.getByText('Showing 0 of 0 tasks')).toBeInTheDocument();
  });
});

