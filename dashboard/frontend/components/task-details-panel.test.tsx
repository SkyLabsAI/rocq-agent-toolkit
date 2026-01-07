import { fireEvent, render, screen, waitFor } from '@testing-library/react';
import React from 'react';

import type { TaskOutput } from '@/types/types';

import TaskDetailsPanel from './task-details-panel';

describe('TaskDetailsPanel', () => {
  const mockTask: TaskOutput = {
    run_id: 'run_1',
    task_kind: 'FullProofTask',
    task_id: 'task_001',
    trace_id: 'trace_001',
    timestamp_utc: '2024-01-01T00:00:00Z',
    agent_name: 'test-agent',
    status: 'Success',
    results: {
      side_effects: {
        doc_interaction: 'Sample interaction',
      },
    },
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
      custom: {
        custom_metric_1: 'value1',
        custom_metric_2: 42,
      },
    },
  };

  const mockOnClose = jest.fn();
  const mockOpenCodeModal = jest.fn();

  // Create a container for portal rendering
  let portalRoot: HTMLElement;

  beforeEach(() => {
    jest.clearAllMocks();
    portalRoot = document.createElement('div');
    portalRoot.setAttribute('id', 'portal-root');
    document.body.appendChild(portalRoot);
  });

  afterEach(() => {
    document.body.removeChild(portalRoot);
  });

  it('does not render when task is null', () => {
    render(
      <TaskDetailsPanel
        task={null}
        isOpen={false}
        onClose={mockOnClose}
        openCodeModal={mockOpenCodeModal}
      />
    );

    expect(screen.queryByText('Task Details')).not.toBeInTheDocument();
  });

  it('renders the panel when open with task data', async () => {
    render(
      <TaskDetailsPanel
        task={mockTask}
        isOpen={true}
        onClose={mockOnClose}
        openCodeModal={mockOpenCodeModal}
      />
    );

    await waitFor(() => {
      expect(screen.getByText('Task Details')).toBeInTheDocument();
    });
    expect(screen.getByText('task_001')).toBeInTheDocument();
    expect(screen.getByText('trace_001')).toBeInTheDocument();
  });

  it('applies correct animation classes when open', async () => {
    render(
      <TaskDetailsPanel
        task={mockTask}
        isOpen={true}
        onClose={mockOnClose}
        openCodeModal={mockOpenCodeModal}
      />
    );

    await waitFor(() => {
      const panel = document.querySelector('.translate-x-0');
      expect(panel).toBeInTheDocument();
    });
  });

  it('applies correct animation classes when closed', async () => {
    render(
      <TaskDetailsPanel
        task={mockTask}
        isOpen={false}
        onClose={mockOnClose}
        openCodeModal={mockOpenCodeModal}
      />
    );

    await waitFor(() => {
      const panel = document.querySelector('.translate-x-full');
      expect(panel).toBeInTheDocument();
    });
  });

  it('displays task info correctly', () => {
    render(
      <TaskDetailsPanel
        task={mockTask}
        isOpen={true}
        onClose={mockOnClose}
        openCodeModal={mockOpenCodeModal}
      />
    );

    expect(screen.getByText('Task ID')).toBeInTheDocument();
    expect(screen.getByText('task_001')).toBeInTheDocument();
    expect(screen.getByText('Trace ID')).toBeInTheDocument();
    expect(screen.getByText('trace_001')).toBeInTheDocument();
    expect(screen.getByText('Task Kind')).toBeInTheDocument();
    expect(screen.getByText('Status')).toBeInTheDocument();
  });

  it('displays performance metrics correctly', () => {
    render(
      <TaskDetailsPanel
        task={mockTask}
        isOpen={true}
        onClose={mockOnClose}
        openCodeModal={mockOpenCodeModal}
      />
    );

    expect(screen.getByText('Performance Metrics')).toBeInTheDocument();
    expect(screen.getByText('Execution Time')).toBeInTheDocument();
    expect(screen.getByText('1.50s')).toBeInTheDocument();
    expect(screen.getByText('CPU Time')).toBeInTheDocument();
    expect(screen.getByText('1.20s')).toBeInTheDocument();
    expect(screen.getByText('GPU Time')).toBeInTheDocument();
    expect(screen.getByText('0.30s')).toBeInTheDocument();
  });

  it('displays custom metrics when available', () => {
    render(
      <TaskDetailsPanel
        task={mockTask}
        isOpen={true}
        onClose={mockOnClose}
        openCodeModal={mockOpenCodeModal}
      />
    );

    expect(screen.getByText('Custom Metrics')).toBeInTheDocument();
    expect(screen.getByText('custom_metric_1')).toBeInTheDocument();
    expect(screen.getByText('value1')).toBeInTheDocument();
    expect(screen.getByText('custom_metric_2')).toBeInTheDocument();
    expect(screen.getByText('42')).toBeInTheDocument();
  });

  it('does not display custom metrics section when not available', () => {
    const taskWithoutCustomMetrics = {
      ...mockTask,
      metrics: {
        ...mockTask.metrics,
        custom: null,
      },
    };

    render(
      <TaskDetailsPanel
        task={taskWithoutCustomMetrics}
        isOpen={true}
        onClose={mockOnClose}
        openCodeModal={mockOpenCodeModal}
      />
    );

    // Should have Performance Metrics but not Custom Metrics
    const customMetricsHeaders = screen.queryAllByText('Custom Metrics');
    expect(customMetricsHeaders.length).toBe(0);
  });

  it('toggles task result expansion', () => {
    render(
      <TaskDetailsPanel
        task={mockTask}
        isOpen={true}
        onClose={mockOnClose}
        openCodeModal={mockOpenCodeModal}
      />
    );

    const toggleButton = screen.getByText(/Task Result/);
    expect(screen.getByText('Sample interaction')).toBeInTheDocument();

    // Click to expand
    fireEvent.click(toggleButton);
    expect(
      screen.getByText(/Task Result \(Full JSON\)/)
    ).toBeInTheDocument();

    // Click to collapse
    fireEvent.click(toggleButton);
    expect(screen.getByText('Sample interaction')).toBeInTheDocument();
  });

  it('calls onClose when close button is clicked', async () => {
    render(
      <TaskDetailsPanel
        task={mockTask}
        isOpen={true}
        onClose={mockOnClose}
        openCodeModal={mockOpenCodeModal}
      />
    );

    await waitFor(() => {
      expect(screen.getByText('Task Details')).toBeInTheDocument();
    });

    const closeButton = screen.getByTitle('Close');
    fireEvent.click(closeButton);

    expect(mockOnClose).toHaveBeenCalledTimes(1);
  });

  it('calls onClose when backdrop is clicked', async () => {
    render(
      <TaskDetailsPanel
        task={mockTask}
        isOpen={true}
        onClose={mockOnClose}
        openCodeModal={mockOpenCodeModal}
      />
    );

    await waitFor(() => {
      const backdrop = document.querySelector('.bg-black\\/50');
      expect(backdrop).toBeInTheDocument();
    });

    const backdrop = document.querySelector('.bg-black\\/50');
    if (backdrop) {
      fireEvent.click(backdrop);
    }

    expect(mockOnClose).toHaveBeenCalledTimes(1);
  });

  it('calls openCodeModal when View Logs button is clicked', () => {
    render(
      <TaskDetailsPanel
        task={mockTask}
        isOpen={true}
        onClose={mockOnClose}
        openCodeModal={mockOpenCodeModal}
      />
    );

    const viewLogsButton = screen.getByText('View Logs');
    fireEvent.click(viewLogsButton);

    expect(mockOpenCodeModal).toHaveBeenCalledTimes(1);
    expect(mockOpenCodeModal).toHaveBeenCalledWith(mockTask);
  });

  it('handles task without trace_id', () => {
    const taskWithoutTraceId = {
      ...mockTask,
      trace_id: undefined,
    };

    render(
      <TaskDetailsPanel
        task={taskWithoutTraceId}
        isOpen={true}
        onClose={mockOnClose}
        openCodeModal={mockOpenCodeModal}
      />
    );

    expect(screen.getByText('Not found')).toBeInTheDocument();
  });
});

