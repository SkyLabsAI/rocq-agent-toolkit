'use client';

import { useRouter } from 'next/navigation';
import React, { useEffect, useState } from 'react';

import { StatusBadge } from '@/components/base/statusBadge';
import { Button } from '@/components/base/ui/button';
import TaskDetailsModal from '@/features/task-details-modal';
import { ChevronUpIcon } from '@/icons/chevron-up';
import { getRunDetails } from '@/services/dataservice';
import type { TaskOutput } from '@/types/types';

interface TaskDetailsPageContentProps {
  runId: string;
  taskId: string;
}

const TaskDetailsPageContent: React.FC<TaskDetailsPageContentProps> = ({
  runId,
  taskId,
}) => {
  const router = useRouter();
  const [task, setTask] = useState<TaskOutput | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [expandedResults, setExpandedResults] = useState(false);
  const [isLogsModalOpen, setIsLogsModalOpen] = useState(false);

  useEffect(() => {
    const fetchTaskDetails = async () => {
      setLoading(true);
      setError(null);

      try {
        const details = await getRunDetails([runId]);
        if (details.length > 0) {
          const foundTask = details[0].tasks.find(t => t.task_id === taskId);
          if (foundTask) {
            setTask(foundTask);
          } else {
            setError('Task not found');
          }
        } else {
          setError('Run not found');
        }
      } catch (err) {
        setError(
          err instanceof Error ? err.message : 'Failed to fetch task details'
        );
      } finally {
        setLoading(false);
      }
    };

    fetchTaskDetails();
  }, [runId, taskId]);

  const handleBack = () => {
    router.push(`/runs/${runId}`);
  };

  const toggleResultExpansion = () => {
    setExpandedResults(prev => !prev);
  };

  const openLogsModal = () => {
    setIsLogsModalOpen(true);
  };

  const closeLogsModal = () => {
    setIsLogsModalOpen(false);
  };

  if (loading) {
    return (
      <div className='flex items-center justify-center min-h-screen bg-elevation-surface'>
        <div className='text-center flex flex-col gap-5 justify-center items-center'>
          <div className='animate-spin rounded-full h-12 w-12 border-b-2 border-elevation-surface-overlay'></div>
          <p className='font-noto-sans text-sm text-text m-0'>
            Loading task details...
          </p>
        </div>
      </div>
    );
  }

  if (error || !task) {
    return (
      <div className='flex items-center justify-center min-h-screen bg-elevation-surface'>
        <div className='text-center'>
          <p className='font-noto-sans text-sm text-text-danger mb-4'>
            Error: {error || 'Task not found'}
          </p>
          <button
            className='px-4 py-2 bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg text-text hover:bg-elevation-surface-overlay transition-colors'
            onClick={handleBack}
          >
            Go Back to Run Details
          </button>
        </div>
      </div>
    );
  }

  return (
    <div className='min-h-screen bg-elevation-surface p-6'>
      <div className='max-w-5xl mx-auto'>
        {/* Header */}
        <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg mb-6'>
          <div className='flex items-center justify-between px-6 py-4'>
            <div className='flex items-center gap-3'>
              <button
                title='Back to Run Details'
                onClick={handleBack}
                className='p-0 hover:bg-background-neutral-hovered rounded-lg w-[38px] h-[38px]'
              >
                <ChevronUpIcon className='rotate-90 size-6 m-auto' />
              </button>
              <div className='flex flex-col gap-1'>
                <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                  Task Details
                </p>
                <p className='font-noto-sans font-semibold text-sm text-text'>
                  {task.task_id}
                </p>
              </div>
            </div>
            <StatusBadge status={task.status} />
          </div>
        </div>

        {/* Content */}
        <div className='space-y-6'>
          {/* Task Info Section */}
          <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg p-6'>
            <p className='font-noto-sans font-semibold text-base text-text mb-4'>
              Task Information
            </p>
            <div className='space-y-4'>
              <div className='grid grid-cols-2 gap-4'>
                <div className='flex flex-col gap-1.5'>
                  <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                    Run ID
                  </p>
                  <p className='font-noto-sans font-normal text-sm text-text break-all'>
                    {task.run_id}
                  </p>
                </div>

                <div className='flex flex-col gap-1.5'>
                  <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                    Trace ID
                  </p>
                  <p className='font-noto-sans font-normal text-sm text-text break-all'>
                    {task.trace_id || 'Not found'}
                  </p>
                </div>

                <div className='flex flex-col gap-1.5'>
                  <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                    Task Kind
                  </p>
                  <p className='font-noto-sans font-normal text-sm text-text'>
                    {typeof task.task_kind === 'string'
                      ? task.task_kind
                      : task.task_kind?.kind || 'Not found'}
                  </p>
                </div>

                <div className='flex flex-col gap-1.5'>
                  <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                    Agent Name
                  </p>
                  <p className='font-noto-sans font-normal text-sm text-text'>
                    {task.agent_name || 'Not found'}
                  </p>
                </div>

                <div className='flex flex-col gap-1.5'>
                  <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                    Timestamp
                  </p>
                  <p className='font-noto-sans font-normal text-sm text-text'>
                    {new Date(task.timestamp_utc).toLocaleString()}
                  </p>
                </div>
              </div>
            </div>
          </div>

          {/* Performance Metrics */}
          <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg p-6'>
            <p className='font-noto-sans font-semibold text-base text-text mb-4'>
              Performance Metrics
            </p>
            <div className='space-y-4'>
              <div className='grid grid-cols-2 gap-4'>
                <div className='flex flex-col gap-1.5'>
                  <p className='font-inter font-normal text-sm text-text-disabled'>
                    Execution Time
                  </p>
                  <p className='font-inter font-normal text-sm text-text'>
                    {`${task.metrics.resource_usage.execution_time_sec.toFixed(2)}s`}
                  </p>
                </div>

                <div className='flex flex-col gap-1.5'>
                  <p className='font-inter font-normal text-sm text-text-disabled'>
                    CPU Time
                  </p>
                  <p className='font-inter font-normal text-sm text-text'>
                    {task.metrics?.resource_usage?.cpu_time_sec.toFixed(2)}s
                  </p>
                </div>

                <div className='flex flex-col gap-1.5'>
                  <p className='font-inter font-normal text-sm text-text-disabled'>
                    GPU Time
                  </p>
                  <p className='font-inter font-normal text-sm text-text'>
                    {`${task.metrics.resource_usage.gpu_time_sec.toFixed(2)}s`}
                  </p>
                </div>

                <div className='flex flex-col gap-1.5'>
                  <p className='font-inter font-normal text-sm text-text-disabled'>
                    LLM Calls
                  </p>
                  <p className='font-inter font-normal text-sm text-text'>
                    {task.metrics?.llm_invocation_count || '_'}
                  </p>
                </div>
              </div>

              <div className='grid grid-cols-3 gap-4'>
                <div className='flex flex-col gap-1.5'>
                  <p className='font-inter font-normal text-sm text-text-disabled'>
                    Total Tokens
                  </p>
                  <p className='font-inter font-normal text-sm text-text'>
                    {task.metrics?.token_counts?.total_tokens?.toLocaleString() ||
                      '_'}
                  </p>
                </div>

                <div className='flex flex-col gap-1.5'>
                  <p className='font-inter font-normal text-sm text-text-disabled'>
                    Input Tokens
                  </p>
                  <p className='font-inter font-normal text-sm text-text'>
                    {task.metrics?.token_counts?.input_tokens?.toLocaleString() ||
                      '_'}
                  </p>
                </div>

                <div className='flex flex-col gap-1.5'>
                  <p className='font-inter font-normal text-sm text-text-disabled'>
                    Output Tokens
                  </p>
                  <p className='font-inter font-normal text-sm text-text'>
                    {task.metrics?.token_counts?.output_tokens?.toLocaleString() ||
                      '_'}
                  </p>
                </div>
              </div>
            </div>
          </div>

          {/* Custom Metrics */}
          {task.metrics?.custom &&
            Object.keys(task.metrics.custom).length > 0 && (
              <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg p-6'>
                <p className='font-noto-sans font-semibold text-base text-text mb-4'>
                  Custom Metrics
                </p>
                <div className='grid grid-cols-2 gap-4'>
                  {Object.entries(task.metrics.custom).map(([key, value]) => (
                    <div key={key} className='flex flex-col gap-1.5'>
                      <p className='font-inter font-normal text-sm text-text-disabled'>
                        {key}
                      </p>
                      <p className='font-inter font-normal text-sm text-text'>
                        {String(value)}
                      </p>
                    </div>
                  ))}
                </div>
              </div>
            )}

          {/* Task Result */}
          <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg p-6'>
            <button
              onClick={toggleResultExpansion}
              className='flex items-center gap-2 font-inter font-semibold text-base text-text hover:text-text-disabled transition-colors mb-4'
            >
              <ChevronUpIcon
                className={`size-4 transition-transform ${
                  expandedResults ? 'rotate-180' : ''
                }`}
              />
              Task Result
              {expandedResults ? ' (Full JSON)' : ''}
            </button>
            <div className='bg-elevation-surface-sunken rounded p-4 max-h-96 overflow-auto'>
              <pre className='font-inter font-normal text-sm text-text whitespace-pre-wrap'>
                {expandedResults
                  ? task.results
                    ? JSON.stringify(task.results, null, 2)
                    : 'No results available.'
                  : task.results?.side_effects?.doc_interaction
                    ? typeof task.results.side_effects.doc_interaction ===
                      'string'
                      ? task.results.side_effects.doc_interaction
                      : JSON.stringify(
                          task.results.side_effects.doc_interaction,
                          null,
                          2
                        )
                    : 'No doc interaction results available.'}
              </pre>
            </div>
          </div>

          {/* Action Buttons */}
          <div className='flex gap-4'>
            <Button
              variant='default'
              onClick={openLogsModal}
              className='flex-1'
            >
              View Detailed Logs
            </Button>
            <Button variant='outline' onClick={handleBack} className='flex-1'>
              Back to Run Details
            </Button>
          </div>
        </div>
      </div>

      {/* Logs Modal */}
      <TaskDetailsModal
        isOpen={isLogsModalOpen}
        onClose={closeLogsModal}
        details={task.results as Record<string, unknown> | null}
        title={`Task Logs - ${task.task_id}`}
        taskId={task.task_id}
      />
    </div>
  );
};

export default TaskDetailsPageContent;
