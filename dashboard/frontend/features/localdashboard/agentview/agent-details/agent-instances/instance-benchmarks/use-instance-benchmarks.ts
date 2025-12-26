import { useCallback, useState } from 'react';

import { getRunsByInstance } from '@/services/dataservice';
import { type Run } from '@/types/types';

export const useInstanceBenchmarks = (
  instanceChecksum: string,
  datasetId: string
) => {
  const [runs, setRuns] = useState<Run[]>([]);
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const fetchRuns = useCallback(async () => {
    setIsLoading(true);
    setError(null);

    try {
      // Fetch all runs for this instance
      const allRuns = await getRunsByInstance(instanceChecksum);
      // Filter runs for the specific dataset
      const filteredRuns = allRuns.filter(run => run.dataset_id === datasetId);
      setRuns(filteredRuns);
    } catch (err) {
      setError(err instanceof Error ? err.message : 'Failed to fetch data');
    } finally {
      setIsLoading(false);
    }
  }, [instanceChecksum, datasetId]);

  return {
    runs,
    isLoading,
    error,
    fetchRuns,
  };
};
