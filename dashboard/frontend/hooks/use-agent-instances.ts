import { useCallback, useState } from 'react';

import { getAgentInstances } from '@/services/dataservice';
import { type AgentInstanceSummary } from '@/types/types';

export const useAgentInstances = (agentClsChecksum: string) => {
  const [instances, setInstances] = useState<AgentInstanceSummary[]>([]);
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [isOpen, setIsOpen] = useState(false);

  const fetchInstances = useCallback(async () => {
    setIsLoading(true);
    setError(null);

    try {
      const data = await getAgentInstances(agentClsChecksum);
      setInstances(data);
    } catch (err) {
      setError(
        err instanceof Error ? err.message : 'Failed to fetch instances'
      );
    } finally {
      setIsLoading(false);
    }
  }, [agentClsChecksum]);

  const toggleDetails = () => {
    const newIsOpen = !isOpen;
    setIsOpen(newIsOpen);
    if (newIsOpen && instances.length === 0) {
      fetchInstances();
    }
  };

  return {
    instances,
    isLoading,
    error,
    isOpen,
    toggleDetails,
    fetchInstances,
  };
};
