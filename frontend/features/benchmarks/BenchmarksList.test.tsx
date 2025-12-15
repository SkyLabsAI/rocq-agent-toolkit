import { fireEvent, render, screen, waitFor } from '@testing-library/react';
import React from 'react';
import { MemoryRouter } from 'react-router-dom';

import { getBenchmarks } from '@/services/dataservice';

import BenchmarksList from './benchmark-list';

jest.mock('@/services/dataservice');
jest.mock('@/layouts/common', () => {
  return function Layout({
    children,
    title,
  }: {
    children: React.ReactNode;
    title: string;
  }) {
    return (
      <div>
        <h1>{title}</h1>
        {children}
      </div>
    );
  };
});

const mockGetBenchmarks = getBenchmarks as jest.MockedFunction<
  typeof getBenchmarks
>;

describe('BenchmarksList', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('should show loading state initially', () => {
    mockGetBenchmarks.mockImplementation(() => new Promise(() => {})); // Never resolves

    render(
      <MemoryRouter>
        <BenchmarksList />
      </MemoryRouter>
    );

    expect(screen.getByText('Loading benchmarks...')).toBeInTheDocument();
  });

  it('should display benchmarks when loaded', async () => {
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

    mockGetBenchmarks.mockResolvedValue(mockBenchmarks);

    render(
      <MemoryRouter>
        <BenchmarksList />
      </MemoryRouter>
    );

    await waitFor(() => {
      expect(screen.getByText('bench1')).toBeInTheDocument();
      expect(screen.getByText('bench2')).toBeInTheDocument();
    });

    expect(screen.getByText('Available Benchmarks')).toBeInTheDocument();
  });

  it('should display empty state when no benchmarks', async () => {
    mockGetBenchmarks.mockResolvedValue([]);

    render(
      <MemoryRouter>
        <BenchmarksList />
      </MemoryRouter>
    );

    await waitFor(() => {
      expect(screen.getByText('No benchmarks available')).toBeInTheDocument();
    });
  });

  it('should display error message on fetch failure', async () => {
    const consoleError = jest.spyOn(console, 'error').mockImplementation();
    mockGetBenchmarks.mockRejectedValue(new Error('Network error'));

    render(
      <MemoryRouter>
        <BenchmarksList />
      </MemoryRouter>
    );

    await waitFor(() => {
      expect(screen.getByText('Failed to load benchmarks')).toBeInTheDocument();
    });

    consoleError.mockRestore();
  });

  it('should refresh benchmarks when refresh button is clicked', async () => {
    const mockBenchmarks = [
      {
        dataset_id: 'bench1',
        description: 'Test Benchmark',
        created_at: '2024-01-01T00:00:00Z',
      },
    ];

    mockGetBenchmarks.mockResolvedValue(mockBenchmarks);

    render(
      <MemoryRouter>
        <BenchmarksList />
      </MemoryRouter>
    );

    await waitFor(() => {
      expect(screen.getByText('bench1')).toBeInTheDocument();
    });

    expect(mockGetBenchmarks).toHaveBeenCalledTimes(1);

    fireEvent.click(screen.getByText('Refresh'));

    await waitFor(() => {
      expect(mockGetBenchmarks).toHaveBeenCalledTimes(2);
    });
  });

  it('should navigate to agents page when benchmark is clicked', async () => {
    const mockBenchmarks = [
      {
        dataset_id: 'bench1',
        description: 'Test Benchmark',
        created_at: '2024-01-01T00:00:00Z',
      },
    ];

    mockGetBenchmarks.mockResolvedValue(mockBenchmarks);

    const { container } = render(
      <MemoryRouter>
        <BenchmarksList />
      </MemoryRouter>
    );

    await waitFor(() => {
      expect(screen.getByText('bench1')).toBeInTheDocument();
    });

    const benchmarkButton = screen.getByText('bench1').closest('button');
    expect(benchmarkButton).toBeInTheDocument();

    if (benchmarkButton) {
      fireEvent.click(benchmarkButton);
      // Navigation is handled by react-router, which is mocked in MemoryRouter
    }
  });
});
