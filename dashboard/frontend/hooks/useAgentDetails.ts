import { useState } from "react";
import { useRouter } from "next/navigation";
import { TaskOutput, AgentRun } from "@/types/types";
import { getDetails, getRunDetails, getObservabilityLogs } from "@/services/dataservice";
import { Run } from "@/contexts/SelectedRunContext";

interface ModalState {
  isOpen: boolean;
  selectedTask: TaskOutput | null;
  logs: Record<string, unknown> | null;
}

export const useAgentDetails = (agent_name: string) => {
  const [loading, setLoading] = useState<boolean>(false);
  const [taskDetails, setTaskDetails] = useState<TaskOutput[]>([]);
  const [runDetails, setRunDetails] = useState<AgentRun[]>([]);
  const [runTaskDetails, setRunTaskDetails] = useState<Map<string, TaskOutput[]>>(new Map());
  const [loadingRunDetails, setLoadingRunDetails] = useState<Set<string>>(new Set());
  const [isOpen, setIsOpen] = useState<boolean>(false);
  const [modalState, setModalState] = useState<ModalState>({
    isOpen: false,
    selectedTask: null,
    logs: null
  });
  const [selectedRuns, setSelectedRuns] = useState<string[]>([]);
  const [expandedRuns, setExpandedRuns] = useState<Set<string>>(new Set());
  const [loadingLogs, setLoadingLogs] = useState<string | null>(null);
  const router = useRouter();

  const openDetails = async () => {
    setLoading(true);
    try {
      const data = await getDetails(agent_name);
      setRunDetails(data);
      setTaskDetails([]);
    } catch (error) {
      console.error(error);
    } finally {
      setLoading(false);
    }
  };

  const toggleDetails = () => {
    return isOpen
      ? setIsOpen(false)
      : openDetails().then(() => setIsOpen(true));
  };

  const openCodeModal = async (task: TaskOutput) => {
    const taskKey = `${task.run_id}-${task.task_id}`;
    setLoadingLogs(taskKey);
    
    try {
      const logs = await getObservabilityLogs(task.run_id, task.task_id);
      
      setModalState({
        isOpen: true,
        selectedTask: task,
        logs: logs
      });
    } catch (error) {
      console.error('Error fetching observability logs:', error);
      setModalState({
        isOpen: true,
        selectedTask: task,
        logs: { error: 'Failed to load logs' }
      });
    } finally {
      setLoadingLogs(null);
    }
  };

  const closeModal = () => {
    setModalState({
      isOpen: false,
      selectedTask: null,
      logs: null
    });
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
    } catch (error) {
      console.error('Error fetching run details:', error);
    } finally {
      setLoadingRunDetails(prev => {
        const newSet = new Set(prev);
        uniqueRunIds.forEach(id => newSet.delete(id));
        return newSet;
      });
    }
  };

  const toggleRunExpansion = (runId: string) => {
    setExpandedRuns(prev => {
      const newSet = new Set(prev);
      if (newSet.has(runId)) {
        newSet.delete(runId);
      } else {
        newSet.add(runId);
        // Fetch run details if not already loaded
        if (!runTaskDetails.has(runId)) {
          fetchRunDetails([runId]);
        }
      }
      return newSet;
    });
  };

  const compareSelected = () => {
    if (selectedRuns.length < 1) return;
    const query = new URLSearchParams({
      agent: agent_name,
      runs: selectedRuns.join(',')
    }).toString();
    router.push(`/admin/compare?${query}`);
  };

  const toggleRunSelection = (run: Run) => {
    setSelectedRuns(prev => 
      prev.includes(run.run_id) 
        ? prev.filter(id => id !== run.run_id)
        : [...prev, run.run_id]
    );
  };

  const clearSelectedRuns = () => {
    setSelectedRuns([]);
  };

  return {
    loading,
    taskDetails,
    runDetails,
    runTaskDetails,
    loadingRunDetails,
    isOpen,
    modalState,
    selectedRuns,
    expandedRuns,
    loadingLogs,
    openDetails,
    toggleDetails,
    openCodeModal,
    closeModal,
    fetchRunDetails,
    toggleRunExpansion,
    compareSelected,
    toggleRunSelection,
    clearSelectedRuns,
  };
};