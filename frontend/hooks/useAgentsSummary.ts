import { useEffect, useState } from 'react';
import {
  AgentSummaryTemp,
  fetchAgentSummaries,
  getData,
  getObservabilityLogs,
} from '@/services/dataservice';
import { AgentSummary, TaskOutput } from '@/types/types';

interface ModalState {
  isOpen: boolean;
  selectedTask: TaskOutput | null;
  logs: Record<string, unknown> | null;
}

export const useAgents = () => {
  const [agentData, setAgentData] = useState<AgentSummary[]>([]);
  const [agentDetailData, setAgentDetailData] = useState<AgentSummaryTemp[]>(
    []
  );
  const [isLoading, setIsLoading] = useState(true);

  const [modalState, setModalState] = useState<ModalState>({
    isOpen: false,
    selectedTask: null,
    logs: null,
  });
  const [loadingLogs, setLoadingLogs] = useState<string | null>(null);

  const fetchData = async () => {
    setIsLoading(true);
    const data = await getData();
    const detailData = await fetchAgentSummaries();
    setAgentData(data);
    setAgentDetailData(detailData);
    setIsLoading(false);
  };

  useEffect(() => {
    fetchData();
  }, []);

  const openCodeModal = async (task: TaskOutput) => {
    const taskKey = `${task.run_id}-${task.task_id}`;
    setLoadingLogs(taskKey);

    try {
      const logs = await getObservabilityLogs(task.run_id, task.task_id);

      setModalState({
        isOpen: true,
        selectedTask: task,
        logs: logs,
      });
    } catch (error) {
      console.error('Error fetching observability logs:', error);
      setModalState({
        isOpen: true,
        selectedTask: task,
        logs: { error: 'Failed to load logs' },
      });
    } finally {
      setLoadingLogs(null);
    }
  };

  const closeModal = () => {
    setModalState({
      isOpen: false,
      selectedTask: null,
      logs: null,
    });
  };

  return {
    agentData,
    agentDetailData,
    isLoading,
    openCodeModal,
    closeModal,
    modalState,
    loadingLogs,
  };
};
