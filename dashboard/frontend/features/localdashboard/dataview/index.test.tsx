import { render, screen } from '@testing-library/react';
import React from 'react';
import { MemoryRouter } from 'react-router-dom';

import { useBenchmarks } from '@/hooks/use-dataview';

import DataView from './index';

jest.mock('@/hooks/use-dataview');
jest.mock('./data-item', () => ({
  DataItem: ({ benchmark }: { benchmark: { dataset_id: string } }) => (
    <div data-testid={`data-item-${benchmark.dataset_id}`}>
      {benchmark.dataset_id}
    </div>
  ),
}));
jest.mock('@/components/global-sticky-compare-bar', () => ({
  __esModule: true,
  GlobalStickyCompareBar: () => (
    <div data-testid='global-sticky-compare-bar'>Compare Bar</div>
  ),
}));

const mockUseBenchmarks = useBenchmarks as jest.MockedFunction<
  typeof useBenchmarks
>;

describe('DataView', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('should render benchmarks', () => {
    const mockBenchmarks = [
      {
        dataset_id: 'bench1',
        description: 'Test Benchmark 1',
        created_at: '2024-01-01T00:00:00Z',
      },
      {
        dataset_id: 'bench2',
        description: 'Test Benchmark 2',
        created_at: '2024-01-02T00:00:00Z',
      },
    ];

    mockUseBenchmarks.mockReturnValue({
      benchmarks: mockBenchmarks,
      loading: false,
      benchmarkAgents: new Map(),
      fetchAgentsForBenchmark: jest.fn(),
    });

    render(
      <MemoryRouter>
        <DataView />
      </MemoryRouter>
    );

    expect(screen.getByTestId('data-item-bench1')).toBeInTheDocument();
    expect(screen.getByTestId('data-item-bench2')).toBeInTheDocument();
    expect(screen.getByTestId('global-sticky-compare-bar')).toBeInTheDocument();
  });

  it('should render empty state when no benchmarks', () => {
    mockUseBenchmarks.mockReturnValue({
      benchmarks: [],
      loading: false,
      benchmarkAgents: new Map(),
      fetchAgentsForBenchmark: jest.fn(),
    });

    render(
      <MemoryRouter>
        <DataView />
      </MemoryRouter>
    );

    expect(screen.queryByTestId(/data-item/)).not.toBeInTheDocument();
  });

  it('should render with GlobalCompareProvider', () => {
    mockUseBenchmarks.mockReturnValue({
      benchmarks: [
        {
          dataset_id: 'bench1',
          description: 'Test',
          created_at: '2024-01-01T00:00:00Z',
        },
      ],
      loading: false,
      benchmarkAgents: new Map(),
      fetchAgentsForBenchmark: jest.fn(),
    });

    render(
      <MemoryRouter>
        <DataView />
      </MemoryRouter>
    );

    // Should render without errors (GlobalCompareProvider wraps the content)
    expect(screen.getByTestId('data-item-bench1')).toBeInTheDocument();
  });
});
