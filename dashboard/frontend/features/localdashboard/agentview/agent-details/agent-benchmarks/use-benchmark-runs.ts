import { useCallback, useState } from 'react';

import { getDetailsForDataset } from '@/services/dataservice';
import { type AgentRun, type Run } from '@/types/types';

export const useAgentBenchmarks = (agentName: string, datasetId: string) => {
  const [runs, setRuns] = useState<Run[]>([]);
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const fetchRuns = useCallback(async () => {
    setIsLoading(true);
    setError(null);

    try {
      const data: AgentRun[] = await getDetailsForDataset(datasetId, agentName);
      // Convert AgentRun[] to Run[] by adding agent_name
      const runsWithAgentName: Run[] = data.map(run => ({
        ...run,
        agent_name: agentName,
      }));
      setRuns(runsWithAgentName);
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
