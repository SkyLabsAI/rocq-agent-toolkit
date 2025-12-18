import { useEffect, useState } from 'react';

import { getBenchmarkAgents, getBenchmarks } from '@/services/dataservice';
import { type AgentSummary, type Benchmark } from '@/types/types';

export const useBenchmarks = () => {
  const [benchmarks, setBenchmarks] = useState<Benchmark[]>([]);
  const [loading, setLoading] = useState<boolean>(true);
  const [error, setError] = useState<string | null>(null);

  const fetchBenchmarks = async () => {
    try {
      setLoading(true);
      setError(null);
      const data = await getBenchmarks();
      setBenchmarks(data);
    } catch (err) {
      setError(
        err instanceof Error ? err.message : 'Failed to fetch benchmarks'
      );
    } finally {
      setLoading(false);
    }
  };

  useEffect(() => {
    fetchBenchmarks();
  }, []);

  return {
    benchmarks,
    loading,
    error,
    refetch: fetchBenchmarks,
  };
};

export const useBenchmarkAgents = (benchmarkId: string | null) => {
  const [agents, setAgents] = useState<AgentSummary[]>([]);
  const [loading, setLoading] = useState<boolean>(false);
  const [error, setError] = useState<string | null>(null);

  const fetchBenchmarkAgents = async (id: string) => {
    try {
      setLoading(true);
      setError(null);
      const data = await getBenchmarkAgents(id);
      setAgents(data.agents);
    } catch (err) {
      setError(
        err instanceof Error ? err.message : 'Failed to fetch benchmark agents'
      );
    } finally {
      setLoading(false);
    }
  };

  useEffect(() => {
    if (benchmarkId) {
      fetchBenchmarkAgents(benchmarkId);
    } else {
      setAgents([]);
      setLoading(false);
      setError(null);
    }
  }, [benchmarkId]);

  return {
    agents,
    loading,
    error,
    refetch: benchmarkId ? () => fetchBenchmarkAgents(benchmarkId) : () => {},
  };
};
