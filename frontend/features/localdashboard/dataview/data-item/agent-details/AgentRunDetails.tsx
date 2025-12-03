import React, { useState, useEffect } from 'react';
import { getRunDetails, getObservabilityLogs } from '@/services/dataservice';
import { RunDetailsResponse, TaskOutput } from '@/types/types';
import { Button } from '@/components/base';
import TaskDetailsModal from '@/features/taskDetailsModal';

interface AgentRunDetailsProps {
  runId: string;
  agentName: string;
  isExpanded: boolean;
}

const AgentRunDetails: React.FC<AgentRunDetailsProps> = ({
  runId,
  agentName,
  isExpanded,
}) => {
  const [runDetails, setRunDetails] = useState<RunDetailsResponse | null>(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [loadingLogs, setLoadingLogs] = useState<string | null>(null);
  const [modalState, setModalState] = useState<{
    isOpen: boolean;
    selectedTask: TaskOutput | null;
    logs: Record<string, unknown> | null;
  }>({
    isOpen: false,
    selectedTask: null,
    logs: null,
  });

  useEffect(() => {
    if (isExpanded && !runDetails) {
      fetchRunDetails();
    }
  }, [isExpanded, runId]);

  const fetchRunDetails = async () => {
    try {
      setLoading(true);
      setError(null);
      const details = await getRunDetails([runId]);
      setRunDetails(details[0]);
    } catch (err) {
      console.error('Error fetching run details:', err);
      setError(err instanceof Error ? err.message : 'Failed to fetch run details');
    } finally {
      setLoading(false);
    }
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

  const getStatusColor = (status: string) => {
    switch (status.toLowerCase()) {
      case 'success':
        return 'text-green-400 bg-green-400/10';
      case 'failure':
        return 'text-red-400 bg-red-400/10';
      default:
        return 'text-gray-400 bg-gray-400/10';
    }
  };

  const formatMetricValue = (value: number, unit?: string) => {
    if (value < 1000) {
      return `${value.toFixed(2)}${unit ? ` ${unit}` : ''}`;
    }
    return `${(value / 1000).toFixed(2)}K${unit ? ` ${unit}` : ''}`;
  };

  if (!isExpanded) return null;

  return (
    <tr>
      <td colSpan={6}>
        <div className='px-8 pt-4 pb-9 bg-elevation-surface rounded-lg '>
          {loading && (
            <div className="flex items-center justify-center py-8">
              <div className="animate-spin rounded-full h-8 w-8 border-b-2 border-primary"></div>
              <span className="ml-3 text-text-secondary">Loading run details...</span>
            </div>
          )}

          {error && (
            <div className="bg-red-500/10 border border-red-500/20 rounded-lg p-4">
              <div className="text-red-400 font-medium">Error loading run details</div>
              <div className="text-red-300 text-sm mt-1">{error}</div>
            </div>
          )}

          {runDetails && !loading && (
            <div className="space-y-4">
              {/* Header */}
              <div className="grid gap-4 px-2.5" style={{ gridTemplateColumns: '30% 1fr 1fr 1fr 1fr 1fr' }}>
                <div className="text-text text-[16px]">Tasks</div>
                <div className="text-text-disabled text-[14px]">Status</div>
                <div className="text-text-disabled text-[14px]">LLM Calls</div>
                <div className="text-text-disabled text-[14px]">Total Tokens</div>
                <div className="text-text-disabled text-[14px]">Execution Time</div>
                <div className="text-text-disabled text-[14px]"></div>
              </div>
              
              {/* Rows */}
              <div className="flex flex-col gap-2 justify-between">
                {runDetails.tasks.map((task: TaskOutput) => (
                  <div key={task.task_id} className="grid gap-4 p-2.5 bg-elevation-surface-raised rounded items-center" style={{ gridTemplateColumns: '30% 1fr 1fr 1fr 1fr 1fr' }}>
                    <div className="text-text text-[14px]">{task.task_id}</div>
                    <div>
                      <span className={` py-1 rounded text-[14px] font-medium ${task.status === 'Success' ? 'text-text-success' : 'text-text-danger'}`}>
                        {task.status}
                      </span>
                    </div>
                    <div className="text-text text-[14px]">{task.metrics.llm_invocation_count}</div>
                    <div className="text-text text-[14px]">{formatMetricValue(task.metrics.token_counts.total_tokens)}</div>
                    <div className="text-text text-[14px]">{task.metrics.resource_usage.execution_time_sec.toFixed(2)}s</div>
                    <div >
                      <Button 
                        className='float-right' 
                        onClick={() => openCodeModal(task)}
                        disabled={loadingLogs === `${task.run_id}-${task.task_id}`}
                      >
                        {loadingLogs === `${task.run_id}-${task.task_id}` ? 'Loading...' : 'View Logs'}
                      </Button>
                    </div>
                  </div>
                ))}
              </div>
            </div>
          )}
        </div>
        
        {/* Task Details Modal */}
        <TaskDetailsModal
          isOpen={modalState.isOpen}
          onClose={closeModal}
          details={modalState.logs}
          title={
            modalState.selectedTask
              ? `Observability Logs - ${modalState.selectedTask.task_id}`
              : 'Task Logs'
          }
          taskId={modalState.selectedTask?.task_id}
        />
      </td>
    </tr>
  );
};

export default AgentRunDetails;