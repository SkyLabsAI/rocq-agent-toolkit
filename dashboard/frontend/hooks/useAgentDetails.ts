import { useState } from 'react';

import { getDetails, getRunDetails } from '@/services/dataservice';
import { type AgentRun, type TaskOutput } from '@/types/types';

export const useAgentDetails = (agent_name: string) => {
  const [loading, setLoading] = useState<boolean>(false);
  const [taskDetails, setTaskDetails] = useState<TaskOutput[]>([]);
  const [runDetails, setRunDetails] = useState<AgentRun[]>([]);
  const [runTaskDetails, setRunTaskDetails] = useState<
    Map<string, TaskOutput[]>
  >(new Map());
  const [loadingRunDetails, setLoadingRunDetails] = useState<Set<string>>(
    new Set()
  );
  const [isOpen, setIsOpen] = useState<boolean>(false);

  const openDetails = async () => {
    setLoading(true);
    try {
      const data = await getDetails(agent_name);
      setRunDetails(data);
      setTaskDetails([]);
    } catch (_error) {
      // Error handling can be added here if needed
    } finally {
      setLoading(false);
    }
  };

  const toggleDetails = () => {
    return isOpen
      ? setIsOpen(false)
      : openDetails().then(() => setIsOpen(true));
  };

  const fetchRunDetails = async (runIds: string[]) => {
    const uniqueRunIds = runIds.filter(id => !runTaskDetails.has(id));

    if (uniqueRunIds.length === 0) return;

    setLoadingRunDetails(prev => {
      const newSet = new Set(prev);
      uniqueRunIds.forEach(id => newSet.add(id));
      return newSet;
    });

    try {
      const runDetailsResponse = await getRunDetails(uniqueRunIds);

      const newRunTaskDetails = new Map(runTaskDetails);
      runDetailsResponse.forEach(runDetail => {
        newRunTaskDetails.set(runDetail.run_id, runDetail.tasks);
      });

      setRunTaskDetails(newRunTaskDetails);
    } catch (_error) {
      // Error handling can be added here if needed
    } finally {
      setLoadingRunDetails(prev => {
        const newSet = new Set(prev);
        uniqueRunIds.forEach(id => newSet.delete(id));
        return newSet;
      });
    }
  };

  return {
    loading,
    taskDetails,
    runDetails,
    runTaskDetails,
    loadingRunDetails,
    isOpen,
    openDetails,
    toggleDetails,
    fetchRunDetails,
  };
};
