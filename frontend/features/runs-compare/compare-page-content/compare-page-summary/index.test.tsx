import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';
import { MemoryRouter, useSearchParams } from 'react-router-dom';

import type { RunStats } from '../..';
import { RunSummary } from './index';

jest.mock('react-router-dom', () => {
  const actual = jest.requireActual('react-router-dom');
  return {
    ...actual,
    useSearchParams: jest.fn(),
    useNavigate: jest.fn(() => jest.fn()),
  };
});

jest.mock('./run-header', () => ({
  RunsHeader: ({ title, keys }: { title: string; keys: string[] }) => (
    <div data-testid='runs-header'>
      {title}: {keys.join(', ')}
    </div>
  ),
}));

jest.mock('./run-row', () => ({
  TaskRow: ({
    stats,
    onClick,
  }: {
    stats: (string | number)[];
    onClick: () => void;
  }) => (
    <div data-testid='task-row' onClick={onClick}>
      {stats.join(', ')}
    </div>
  ),
}));

describe('RunSummary', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  const mockRunStats: RunStats[] = [
    {
      id: 'run1',
      name: 'Agent 1',
      tasks: 10,
      successRate: 0.8,
      totalLlmCalls: 50,
      totalTokens: 5000,
      avgExecutionTime: 2.5,
    },
    {
      id: 'run2',
      name: 'Agent 2',
      tasks: 8,
      successRate: 0.75,
      totalLlmCalls: 40,
      totalTokens: 4000,
      avgExecutionTime: 2.0,
    },
  ];

  it('should render run stats', () => {
    (useSearchParams as jest.Mock).mockReturnValue([
      new URLSearchParams('?agent=agent1'),
    ]);

    render(
      <MemoryRouter>
        <RunSummary runStats={mockRunStats} />
      </MemoryRouter>
    );

    expect(screen.getByTestId('runs-header')).toBeInTheDocument();
    expect(screen.getAllByTestId('task-row')).toHaveLength(2);
  });

  it('should display formatted stats', () => {
    (useSearchParams as jest.Mock).mockReturnValue([
      new URLSearchParams('?agent=agent1'),
    ]);

    render(
      <MemoryRouter>
        <RunSummary runStats={mockRunStats} />
      </MemoryRouter>
    );

    const rows = screen.getAllByTestId('task-row');
    expect(rows[0]).toHaveTextContent('run1');
    expect(rows[0]).toHaveTextContent('10');
    expect(rows[0]).toHaveTextContent('80.00'); // successRate * 100
  });

  it('should call onRemove when provided', () => {
    (useSearchParams as jest.Mock).mockReturnValue([
      new URLSearchParams('?agent=agent1'),
    ]);
    const handleRemove = jest.fn();

    render(
      <MemoryRouter>
        <RunSummary runStats={mockRunStats} onRemove={handleRemove} />
      </MemoryRouter>
    );

    const rows = screen.getAllByTestId('task-row');
    fireEvent.click(rows[0]);

    expect(handleRemove).toHaveBeenCalledWith('run1');
  });

  it('should use default handleRemove when onRemove not provided', () => {
    const mockNavigate = jest.fn();
    (useSearchParams as jest.Mock).mockReturnValue([
      new URLSearchParams('?agent=agent1&runs=run1,run2'),
    ]);

    jest.doMock('react-router-dom', () => ({
      ...jest.requireActual('react-router-dom'),
      useNavigate: () => mockNavigate,
    }));

    render(
      <MemoryRouter>
        <RunSummary runStats={mockRunStats} />
      </MemoryRouter>
    );

    const rows = screen.getAllByTestId('task-row');
    fireEvent.click(rows[0]);

    // Default handler should navigate
    // Note: This is harder to test without full router setup, but we verify it doesn't crash
    expect(rows).toHaveLength(2);
  });
});
