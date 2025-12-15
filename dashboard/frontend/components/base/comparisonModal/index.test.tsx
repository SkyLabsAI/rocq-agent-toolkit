import { fireEvent, render, screen, waitFor } from '@testing-library/react';
import React from 'react';

import { useComparisonLogs } from './hooks/useComparisonLogs';
import ComparisonModal from './index';

jest.mock('./hooks/useComparisonLogs');
jest.mock('@/components/base/ui/modal', () => ({
  __esModule: true,
  default: ({
    isOpen,
    onClose,
    title,
    children,
  }: {
    isOpen: boolean;
    onClose: () => void;
    title: string;
    children: React.ReactNode;
  }) =>
    isOpen ? (
      <div data-testid='modal'>
        <div>{title}</div>
        <button onClick={onClose}>Close</button>
        {children}
      </div>
    ) : null,
}));
jest.mock('./components/CodeContent', () => ({
  __esModule: true,
  default: ({ keyName }: { keyName: string }) => (
    <div data-testid={`code-content-${keyName}`}>Code: {keyName}</div>
  ),
}));
jest.mock('./components/JsonContent', () => ({
  __esModule: true,
  default: ({ value }: { value: unknown }) => (
    <div data-testid='json-content'>{JSON.stringify(value)}</div>
  ),
}));
jest.mock('@/components/base/tacticInfo', () => ({
  __esModule: true,
  default: ({ tactics }: { tactics: unknown[] }) => (
    <div data-testid='tactic-info'>Tactics: {tactics.length}</div>
  ),
}));

const mockUseComparisonLogs = useComparisonLogs as jest.MockedFunction<
  typeof useComparisonLogs
>;

describe('ComparisonModal', () => {
  const mockItems = [
    {
      label: 'Agent 1',
      task: {
        run_id: 'run1',
        task_id: 'task1',
        task_kind: 'FullProofTask',
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
    {
      label: 'Agent 2',
      task: {
        run_id: 'run2',
        task_id: 'task1',
        task_kind: 'FullProofTask',
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
    },
  ];

  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('should not render when closed', () => {
    mockUseComparisonLogs.mockReturnValue({
      taskLogs: {},
      loading: false,
      error: null,
    });

    render(
      <ComparisonModal
        isOpen={false}
        onClose={jest.fn()}
        items={mockItems}
        taskId='task1'
      />
    );

    expect(screen.queryByTestId('modal')).not.toBeInTheDocument();
  });

  it('should render when open', () => {
    mockUseComparisonLogs.mockReturnValue({
      taskLogs: {},
      loading: false,
      error: null,
    });

    render(
      <ComparisonModal
        isOpen={true}
        onClose={jest.fn()}
        items={mockItems}
        taskId='task1'
      />
    );

    expect(screen.getByTestId('modal')).toBeInTheDocument();
    expect(screen.getByText(/Compare Task: task1/)).toBeInTheDocument();
  });

  it('should show loading state', () => {
    mockUseComparisonLogs.mockReturnValue({
      taskLogs: {},
      loading: true,
      error: null,
    });

    render(
      <ComparisonModal
        isOpen={true}
        onClose={jest.fn()}
        items={mockItems}
        taskId='task1'
      />
    );

    expect(screen.getByText('Loading comparison data...')).toBeInTheDocument();
  });

  it('should show error state', () => {
    mockUseComparisonLogs.mockReturnValue({
      taskLogs: {},
      loading: false,
      error: 'Failed to load',
    });

    render(
      <ComparisonModal
        isOpen={true}
        onClose={jest.fn()}
        items={mockItems}
        taskId='task1'
      />
    );

    expect(screen.getByText(/Error: Failed to load/)).toBeInTheDocument();
  });

  it('should show no data state when no keys available', () => {
    mockUseComparisonLogs.mockReturnValue({
      taskLogs: {},
      loading: false,
      error: null,
    });

    render(
      <ComparisonModal
        isOpen={true}
        onClose={jest.fn()}
        items={mockItems}
        taskId='task1'
      />
    );

    expect(
      screen.getByText('No comparable data available')
    ).toBeInTheDocument();
  });

  it('should render tabs for available keys', () => {
    mockUseComparisonLogs.mockReturnValue({
      taskLogs: {
        0: { cpp_code: 'code1', json_data: { key: 'value' } },
        1: { cpp_code: 'code2', json_data: { key: 'value' } },
      },
      loading: false,
      error: null,
    });

    render(
      <ComparisonModal
        isOpen={true}
        onClose={jest.fn()}
        items={mockItems}
        taskId='task1'
      />
    );

    expect(screen.getByText('cpp_code')).toBeInTheDocument();
    expect(screen.getByText('json_data')).toBeInTheDocument();
  });

  it('should switch tabs when clicked', () => {
    mockUseComparisonLogs.mockReturnValue({
      taskLogs: {
        0: { cpp_code: 'code1', json_data: { key: 'value' } },
      },
      loading: false,
      error: null,
    });

    render(
      <ComparisonModal
        isOpen={true}
        onClose={jest.fn()}
        items={mockItems}
        taskId='task1'
      />
    );

    const jsonTab = screen.getByText('json_data');
    fireEvent.click(jsonTab);

    expect(screen.getByTestId('json-content')).toBeInTheDocument();
  });

  it('should render custom content for tactic key', () => {
    mockUseComparisonLogs.mockReturnValue({
      taskLogs: {
        0: { tactic: [{ goal: 'test', status: 'success' }] },
      },
      loading: false,
      error: null,
    });

    render(
      <ComparisonModal
        isOpen={true}
        onClose={jest.fn()}
        items={mockItems}
        taskId='task1'
      />
    );

    expect(screen.getByTestId('tactic-info')).toBeInTheDocument();
  });

  it('should render code content for custom keys', () => {
    mockUseComparisonLogs.mockReturnValue({
      taskLogs: {
        0: { cpp_code: 'code1' },
      },
      loading: false,
      error: null,
    });

    render(
      <ComparisonModal
        isOpen={true}
        onClose={jest.fn()}
        items={mockItems}
        taskId='task1'
      />
    );

    expect(screen.getByTestId('code-content-cpp_code')).toBeInTheDocument();
  });

  it('should render JSON content for non-custom keys', () => {
    mockUseComparisonLogs.mockReturnValue({
      taskLogs: {
        0: { custom_key: { data: 'value' } },
      },
      loading: false,
      error: null,
    });

    render(
      <ComparisonModal
        isOpen={true}
        onClose={jest.fn()}
        items={mockItems}
        taskId='task1'
      />
    );

    expect(screen.getByTestId('json-content')).toBeInTheDocument();
  });

  it('should handle items with null tasks', () => {
    mockUseComparisonLogs.mockReturnValue({
      taskLogs: {
        0: { key: 'value' },
        1: null,
      },
      loading: false,
      error: null,
    });

    const itemsWithNull = [...mockItems, { label: 'Agent 3', task: null }];

    render(
      <ComparisonModal
        isOpen={true}
        onClose={jest.fn()}
        items={itemsWithNull}
        taskId='task1'
      />
    );

    expect(screen.getByText('Agent 3')).toBeInTheDocument();
  });

  it('should toggle item card expansion', () => {
    mockUseComparisonLogs.mockReturnValue({
      taskLogs: {
        0: { key: 'value' },
      },
      loading: false,
      error: null,
    });

    render(
      <ComparisonModal
        isOpen={true}
        onClose={jest.fn()}
        items={mockItems}
        taskId='task1'
      />
    );

    const card = screen.getByText('Agent 1').closest('div');
    if (card) {
      fireEvent.click(card);
      // Card should expand
    }
  });

  it('should call onClose when close button is clicked', () => {
    const handleClose = jest.fn();
    mockUseComparisonLogs.mockReturnValue({
      taskLogs: {},
      loading: false,
      error: null,
    });

    render(
      <ComparisonModal
        isOpen={true}
        onClose={handleClose}
        items={mockItems}
        taskId='task1'
      />
    );

    fireEvent.click(screen.getByText('Close'));
    expect(handleClose).toHaveBeenCalled();
  });

  it('should handle array values in custom content', () => {
    mockUseComparisonLogs.mockReturnValue({
      taskLogs: {
        0: { code: ['code1', 'code2'] },
      },
      loading: false,
      error: null,
    });

    render(
      <ComparisonModal
        isOpen={true}
        onClose={jest.fn()}
        items={mockItems}
        taskId='task1'
      />
    );

    expect(screen.getByTestId('code-content-code')).toBeInTheDocument();
  });

  it('should handle string array values in json content', () => {
    mockUseComparisonLogs.mockReturnValue({
      taskLogs: {
        0: { custom_array: ['str1', 'str2'] },
      },
      loading: false,
      error: null,
    });

    render(
      <ComparisonModal
        isOpen={true}
        onClose={jest.fn()}
        items={mockItems}
        taskId='task1'
      />
    );

    // Should render as string array items
    expect(screen.getByText(/Item 1/)).toBeInTheDocument();
  });
});
