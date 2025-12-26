import { useCallback, useState } from 'react';

import { getDatasetAgentInstances } from '@/services/dataservice';
import { type AgentInstanceSummary } from '@/types/types';

export const useDatasetAgentClass = (
  datasetId: string,
  agentClsChecksum: string
) => {
  const [instances, setInstances] = useState<AgentInstanceSummary[]>([]);
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const fetchInstances = useCallback(async () => {
    setIsLoading(true);
    setError(null);

    try {
      const data = await getDatasetAgentInstances(datasetId, agentClsChecksum);
      setInstances(data);
    } catch (err) {
      setError(
        err instanceof Error ? err.message : 'Failed to fetch instances'
      );
    } finally {
      setIsLoading(false);
    }
  }, [datasetId, agentClsChecksum]);

  return {
    instances,
    isLoading,
    error,
    fetchInstances,
  };
};
