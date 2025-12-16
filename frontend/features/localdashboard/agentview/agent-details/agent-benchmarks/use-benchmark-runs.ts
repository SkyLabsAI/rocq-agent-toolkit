import { useCallback, useState } from 'react';

import { getDetailsForDataset } from '@/services/dataservice';
import { type Run } from '@/types/types';

export const useAgentBenchmarks = (agentName: string, datasetId: string) => {
  const [runs, setRuns] = useState<Run[]>([]);
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const fetchRuns = useCallback(async () => {
    setIsLoading(true);
    setError(null);

    try {
      const data = await getDetailsForDataset(datasetId, agentName);
      setRuns(data);
    } catch (err) {
      setError(err instanceof Error ? err.message : 'Failed to fetch data');
    } finally {
      setIsLoading(false);
    }
  }, [agentName, datasetId]);

  return {
    runs,
    isLoading,
    error,
    fetchRuns,
  };
};
