import { render, screen } from '@testing-library/react';
import React from 'react';

import { type RunTaskCell } from '@/features/runs-compare';

import { type TaskRowData } from '../../../utils';
import {
  extractMetricRows,
  getFlatKeys,
  getNestedValue,
  TaskDetailsTable,
} from './index';

jest.mock('./comparison-row', () => ({
  ComparisonRow: ({ label, values }: { label: string; values: string[] }) => (
    <div data-testid='comparison-row'>
      <div data-testid='label'>{label}</div>
      <div data-testid='values'>{values.join(',')}</div>
    </div>
  ),
}));

describe('TaskDetailsTable', () => {
  const mockTaskRowData: TaskRowData = {
    taskId: 'task1',
    cells: [
      {
        runId: 'run1',
        runName: 'agent1',
        task: {
          run_id: 'run1',
          task_kind: 'FullProofTask',
          task_id: 'task1',
          timestamp_utc: '2024-01-01',
          agent_name: 'agent1',
          status: 'Success',
          results: {},
          metrics: {
            llm_invocation_count: 5,
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
    ],
  };

  const mockDetails: RunTaskCell[] = [
    {
      run: {
        run_id: 'run1',
        agent_name: 'agent1',
        total_tasks: 1,
        tasks: [],
      },
      task: mockTaskRowData.cells[0].task,
    },
  ];

  it('should render task details table', () => {
    render(
      <TaskDetailsTable
        id='task1'
        details={mockDetails}
        taskRowData={mockTaskRowData}
      />
    );

    expect(screen.getByTestId('comparison-row')).toBeInTheDocument();
  });
});

describe('extractMetricRows', () => {
  it('should extract metric rows from task row data', () => {
    const taskRowData: TaskRowData = {
      taskId: 'task1',
      cells: [
        {
          runId: 'run1',
          runName: 'agent1',
          task: {
            run_id: 'run1',
            task_kind: 'FullProofTask',
            task_id: 'task1',
            timestamp_utc: '2024-01-01',
            agent_name: 'agent1',
            status: 'Success',
            results: {},
            metrics: {
              llm_invocation_count: 5,
              token_counts: { total_tokens: 150 },
              resource_usage: { execution_time_sec: 1.0 },
              custom: null,
            },
          },
        },
      ],
    };

    const result = extractMetricRows(taskRowData);

    expect(result.length).toBeGreaterThan(0);
    expect(result[0]).toHaveProperty('key');
    expect(result[0]).toHaveProperty('label');
    expect(result[0]).toHaveProperty('values');
  });

  it('should handle empty cells', () => {
    const taskRowData: TaskRowData = {
      taskId: 'task1',
      cells: [null],
    };

    const result = extractMetricRows(taskRowData);

    expect(result).toEqual([]);
  });
});

describe('getFlatKeys', () => {
  it('should flatten nested objects', () => {
    const obj = {
      token_counts: { total: 10, input: 5 },
      resource_usage: { execution_time: 1.0 },
    };

    const keys = getFlatKeys(obj);

    expect(keys).toContain('token_counts.total');
    expect(keys).toContain('token_counts.input');
    expect(keys).toContain('resource_usage.execution_time');
  });

  it('should handle arrays as values', () => {
    const obj = {
      array: [1, 2, 3],
      nested: { value: 10 },
    };

    const keys = getFlatKeys(obj);

    expect(keys).toContain('array');
    expect(keys).toContain('nested.value');
  });

  it('should handle null and undefined', () => {
    expect(getFlatKeys(null)).toEqual([]);
    expect(getFlatKeys(undefined)).toEqual([]);
  });
});

describe('getNestedValue', () => {
  it('should get nested value by path', () => {
    const obj = {
      metrics: {
        token_counts: {
          total_tokens: 150,
        },
      },
    };

    expect(getNestedValue(obj, 'metrics.token_counts.total_tokens')).toBe(150);
  });

  it('should return undefined for invalid path', () => {
    const obj = { metrics: { token_counts: { total: 150 } } };

    expect(getNestedValue(obj, 'metrics.invalid.path')).toBeUndefined();
  });
});
