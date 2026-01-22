'use client';

import { useRouter } from 'next/navigation';
import React, { useEffect, useState } from 'react';

import Button from '@/components/base/ui/button';
import Modal from '@/components/base/ui/modal';
import VisualizerModal from '@/components/visualizer-modal';
import ObservabilityLogsModal from '@/features/task-details-modal';
import {
  getAgentInstanceTaskRuns,
  getObservabilityLogs,
  getTaskDetails,
} from '@/services/dataservice';
import { type AgentRun, type TaskOutput } from '@/types/types';

interface ProjectTaskDetailsModalProps {
  isOpen: boolean;
  onClose: () => void;
  taskId: number;
  agentInstanceId: string;
  agentChecksum: string;
  agentName: string;
}

const ProjectTaskDetailsModal: React.FC<ProjectTaskDetailsModalProps> = ({
  isOpen,
  onClose,
  taskId,
  agentChecksum,
  agentName,
}) => {
  const router = useRouter();
  const [runs, setRuns] = useState<AgentRun[]>([]);
  const [selectedRunId, setSelectedRunId] = useState<string | null>(null);
  const [taskResult, setTaskResult] = useState<TaskOutput | null>(null);
  const [loadingRuns, setLoadingRuns] = useState(false);
  const [loadingTask, setLoadingTask] = useState(false);
  const [loadingLogs, setLoadingLogs] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [isLogsModalOpen, setIsLogsModalOpen] = useState(false);
  const [logs, setLogs] = useState<Record<string, unknown> | null>(null);
  const [isVisualizerOpen, setIsVisualizerOpen] = useState(false);

  // Fetch runs for the agent instance and task
  useEffect(() => {
    if (isOpen && agentChecksum && taskId) {
      const fetchRuns = async () => {
        try {
          setLoadingRuns(true);
          setError(null);
          const fetchedRuns = await getAgentInstanceTaskRuns(
            agentChecksum,
            taskId
          );
          setRuns(fetchedRuns);
          // Select the first run by default
          if (fetchedRuns.length > 0) {
            setSelectedRunId(fetchedRuns[0].run_id);
          }
        } catch (err) {
          setError(err instanceof Error ? err.message : 'Failed to fetch runs');
        } finally {
          setLoadingRuns(false);
        }
      };

      fetchRuns();
    }
  }, [isOpen, agentChecksum, taskId]);

  // Fetch task result when run is selected
  useEffect(() => {
    if (isOpen && selectedRunId && taskId) {
      const fetchTaskResult = async () => {
        try {
          setLoadingTask(true);
          setError(null);
          const task = await getTaskDetails(selectedRunId, taskId);
          setTaskResult(task);
        } catch (err) {
          setError(
            err instanceof Error ? err.message : 'Failed to fetch task result'
          );
          setTaskResult(null);
        } finally {
          setLoadingTask(false);
        }
      };

      fetchTaskResult();
    }
  }, [isOpen, selectedRunId, taskId]);

  const handleClose = () => {
    setSelectedRunId(null);
    setTaskResult(null);
    setError(null);
    setIsLogsModalOpen(false);
    setLogs(null);
    setIsVisualizerOpen(false);
    onClose();
  };

  const handleViewLogs = async () => {
    if (!selectedRunId || !taskId) return;

    try {
      setLoadingLogs(true);
      const observabilityLogs = await getObservabilityLogs(
        selectedRunId,
        taskId
      );
      setLogs(observabilityLogs);
      setIsLogsModalOpen(true);
    } catch (err) {
      setError(err instanceof Error ? err.message : 'Failed to fetch logs');
    } finally {
      setLoadingLogs(false);
    }
  };

  const handleViewFull = () => {
    if (!selectedRunId) return;
    router.push(`/runs/${selectedRunId}/tasks/${taskId}`);
  };

  const handleVisualize = () => {
    if (!selectedRunId) return;
    const selectedRun = runs.find(r => r.run_id === selectedRunId);
    if (selectedRun) {
      setIsVisualizerOpen(true);
    }
  };

  const selectedRun = runs.find(r => r.run_id === selectedRunId);

  return (
    <Modal
      isOpen={isOpen}
      onClose={handleClose}
      title={`Task: ${taskId} - ${agentName}`}
      size='large'
    >
      <div className='flex flex-col gap-6'>
        {/* Runs Dropdown */}
        <div>
          <h3 className='text-lg font-semibold text-text mb-4'>Runs</h3>
          {loadingRuns ? (
            <div className='flex justify-center py-4'>
              <div className='animate-spin rounded-full h-6 w-6 border-b-2 border-blue-400'></div>
            </div>
          ) : runs.length === 0 ? (
            <div className='text-center py-4 text-text-disabled'>
              No runs found for this agent instance
            </div>
          ) : (
            <select
              value={selectedRunId || ''}
              onChange={e => setSelectedRunId(e.target.value)}
              className='w-full p-3 rounded-lg border bg-elevation-surface border-elevation-surface-overlay text-text font-["Noto_Sans"] text-sm font-normal leading-5 focus:outline-none focus:ring-2 focus:ring-border-focused focus:border-border-focused hover:bg-elevation-surface-raised transition-colors cursor-pointer'
            >
              {runs.map(run => {
                const percentage = (
                  (run.success_count / run.total_tasks) *
                  100
                ).toFixed(1);
                const displayText = `${run.run_id} - ${new Date(run.timestamp_utc).toLocaleString()} (${run.success_count}/${run.total_tasks}, ${percentage}%)`;
                return (
                  <option key={run.run_id} value={run.run_id}>
                    {displayText}
                  </option>
                );
              })}
            </select>
          )}
        </div>

        {/* Task Result */}
        {selectedRunId && (
          <div>
            <h3 className='text-lg font-semibold text-text mb-4'>
              Task Result
            </h3>
            {loadingTask ? (
              <div className='flex justify-center py-8'>
                <div className='animate-spin rounded-full h-8 w-8 border-b-2 border-blue-400'></div>
              </div>
            ) : error ? (
              <div className='text-center py-8 text-text-disabled'>{error}</div>
            ) : taskResult ? (
              <div className='bg-elevation-surface-raised rounded-lg border border-elevation-surface-overlay p-6'>
                <div className='grid grid-cols-2 gap-4 mb-6'>
                  <div>
                    <span className='text-sm text-text-disabled'>Status</span>
                    <p className='text-base font-medium text-text mt-1'>
                      {taskResult.status}
                    </p>
                  </div>
                  <div>
                    <span className='text-sm text-text-disabled'>
                      Task Kind
                    </span>
                    <p className='text-base font-medium text-text mt-1'>
                      {typeof taskResult.task_kind === 'string'
                        ? taskResult.task_kind
                        : taskResult.task_kind.kind}
                    </p>
                  </div>
                  <div>
                    <span className='text-sm text-text-disabled'>
                      LLM Invocations
                    </span>
                    <p className='text-base font-medium text-text mt-1'>
                      {taskResult.metrics.llm_invocation_count}
                    </p>
                  </div>
                  <div>
                    <span className='text-sm text-text-disabled'>
                      Total Tokens
                    </span>
                    <p className='text-base font-medium text-text mt-1'>
                      {taskResult.metrics.token_counts.total_tokens}
                    </p>
                  </div>
                  <div>
                    <span className='text-sm text-text-disabled'>
                      Execution Time
                    </span>
                    <p className='text-base font-medium text-text mt-1'>
                      {taskResult.metrics.resource_usage.execution_time_sec.toFixed(
                        2
                      )}{' '}
                      s
                    </p>
                  </div>
                  <div>
                    <span className='text-sm text-text-disabled'>CPU Time</span>
                    <p className='text-base font-medium text-text mt-1'>
                      {taskResult.metrics.resource_usage.cpu_time_sec.toFixed(
                        2
                      )}{' '}
                      s
                    </p>
                  </div>
                </div>

                {taskResult.results && (
                  <div>
                    <span className='text-sm text-text-disabled block mb-2'>
                      Results
                    </span>
                    <div className='bg-elevation-surface-sunken rounded p-4 max-h-96 overflow-auto'>
                      <pre className='font-mono text-sm text-text whitespace-pre-wrap'>
                        {JSON.stringify(taskResult.results, null, 2)}
                      </pre>
                    </div>
                  </div>
                )}

                {taskResult.failure_reason && (
                  <div className='mt-4'>
                    <span className='text-sm text-text-disabled block mb-2'>
                      Failure Reason
                    </span>
                    <div className='bg-elevation-surface-sunken rounded p-4'>
                      <pre className='font-mono text-sm text-text-danger whitespace-pre-wrap'>
                        {typeof taskResult.failure_reason === 'string'
                          ? taskResult.failure_reason
                          : JSON.stringify(taskResult.failure_reason, null, 2)}
                      </pre>
                    </div>
                  </div>
                )}

                {/* Action Buttons */}
                <div className='flex gap-3 mt-6'>
                  <Button
                    variant='default'
                    onClick={handleViewLogs}
                    disabled={loadingLogs}
                    className='flex-1'
                  >
                    {loadingLogs ? 'Loading...' : 'View Logs'}
                  </Button>
                  <Button
                    variant='default'
                    onClick={handleViewFull}
                    disabled={!selectedRunId}
                    className='flex-1'
                  >
                    View Full
                  </Button>
                  <Button
                    variant='default'
                    onClick={handleVisualize}
                    disabled={!selectedRunId}
                    className='flex-1'
                  >
                    Visualize
                  </Button>
                </div>
              </div>
            ) : (
              <div className='text-center py-8 text-text-disabled'>
                Task not found in selected run
              </div>
            )}
          </div>
        )}
      </div>

      {/* Logs Modal */}
      <ObservabilityLogsModal
        isOpen={isLogsModalOpen}
        onClose={() => setIsLogsModalOpen(false)}
        details={logs}
        title={`Observability Logs - ${taskId}`}
        taskId={taskId}
      />

      {/* Visualizer Modal */}
      {selectedRun && (
        <VisualizerModal
          isOpen={isVisualizerOpen}
          onClose={() => setIsVisualizerOpen(false)}
          runId={selectedRun.run_id}
          runTimestampUtc={selectedRun.timestamp_utc}
          taskId={taskId}
        />
      )}
    </Modal>
  );
};

export default ProjectTaskDetailsModal;
