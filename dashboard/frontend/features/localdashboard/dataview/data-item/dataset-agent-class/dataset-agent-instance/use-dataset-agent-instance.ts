import { useCallback, useState } from 'react';

import { getDatasetInstanceRuns } from '@/services/dataservice';
import { type Run } from '@/types/types';

export const useDatasetAgentInstance = (
  datasetId: string,
  instanceChecksum: string
) => {
  const [runs, setRuns] = useState<Run[]>([]);
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const fetchRuns = useCallback(async () => {
    setIsLoading(true);
    setError(null);

    try {
      const data = await getDatasetInstanceRuns(datasetId, instanceChecksum);
      setRuns(data);
    } catch (err) {
      setError(err instanceof Error ? err.message : 'Failed to fetch runs');
    } finally {
      setIsLoading(false);
    }
  }, [datasetId, instanceChecksum]);

  return {
    runs,
    isLoading,
    error,
    fetchRuns,
  };
};
