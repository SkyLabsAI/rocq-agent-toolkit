import { useEffect, useState } from 'react';
import {
  AgentSummaryTemp,
  fetchAgentSummaries,
  getData,
  getObservabilityLogs,
  refreshData,
} from '@/services/dataservice';
import { AgentSummary, TaskOutput } from '@/types/types';

interface ModalState {
  isOpen: boolean;
  selectedTask: TaskOutput | null;
  logs: Record<string, unknown> | null;
}

export const useAdminDashboard = () => {
  const [agentData, setAgentData] = useState<AgentSummary[]>([]);
  const [agentDetailData, setAgentDetailData] = useState<AgentSummaryTemp[]>(
    []
  );
  const [isRefreshing, setIsRefreshing] = useState(false);
  const [refreshMessage, setRefreshMessage] = useState<string>('');

  const [modalState, setModalState] = useState<ModalState>({
    isOpen: false,
    selectedTask: null,
    logs: null,
  });
  const [loadingLogs, setLoadingLogs] = useState<string | null>(null);

  const fetchData = async () => {
    const data = await getData();
    const detailData = await fetchAgentSummaries();
    setAgentData(data);
    setAgentDetailData(detailData);
  };

  useEffect(() => {
    fetchData();
  }, []);

  const handleRefresh = async () => {
    setIsRefreshing(true);
    setRefreshMessage('');
    try {
      const result = await refreshData();
      if (result.success) {
        setRefreshMessage(result.message);
        await fetchData();
        // Clear message after 3 seconds
        setTimeout(() => setRefreshMessage(''), 3000);
      }
    } catch (error) {
      console.error('Error refreshing data:', error);
      setRefreshMessage('Error refreshing data. Please try again.');
      setTimeout(() => setRefreshMessage(''), 3000);
    } finally {
      setIsRefreshing(false);
    }


    fetchData()
  };

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
    isRefreshing,
    refreshMessage,
    handleRefresh,
    openCodeModal,
    closeModal,
    modalState,
    loadingLogs,
  };
};
