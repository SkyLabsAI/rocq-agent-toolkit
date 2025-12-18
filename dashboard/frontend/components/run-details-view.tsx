import React, { useEffect, useState } from 'react';

import { Button } from '@/components/base/ui/button';
import { ChevronUpIcon } from '@/icons/chevron-up';
import { getRunDetails } from '@/services/dataservice';
import type { TaskOutput } from '@/types/types';

import { StatusBadge } from './base/statusBadge';

interface RunDetailsViewProps {
  run: {
    run_id: string;
    agent_name: string;
    timestamp_utc: string;
    total_tasks: number;
    success_count: number;
    failure_count: number;
  };
  onBack: () => void;
  openCodeModal: (task: TaskOutput) => void;
}

const RunDetailsView: React.FC<RunDetailsViewProps> = ({
  run,
  onBack,
  openCodeModal,
}) => {
  const [taskDetails, setTaskDetails] = useState<TaskOutput[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [expandedResults, setExpandedResults] = useState<Set<string>>(
    new Set()
  );

  const toggleResultExpansion = (taskId: string) => {
    setExpandedResults(prev => {
      const newSet = new Set(prev);
      if (newSet.has(taskId)) {
        newSet.delete(taskId);
      } else {
        newSet.add(taskId);
      }
      return newSet;
    });
  };

  useEffect(() => {
    const fetchRunDetails = async () => {
      setLoading(true);
      setError(null);

      try {
        const runDetailsResponse = await getRunDetails([run.run_id]);
        if (runDetailsResponse.length > 0) {
          setTaskDetails(runDetailsResponse[0].tasks);
        }
      } catch (err) {
        setError(
          err instanceof Error ? err.message : 'Failed to fetch run details'
        );
      } finally {
        setLoading(false);
      }
    };

    fetchRunDetails();
  }, [run.run_id]);

  if (loading) {
    return (
      <div className=' bg-elevation-surface z-50 flex items-center justify-center rounded-lg py-10'>
        <div className='text-center flex flex-col gap-5 justify-center items-center'>
          <div className='animate-spin rounded-full h-12 w-12 border-b-2 border-elevation-surface-overlay'></div>
          <p className='font-noto-sans text-sm text-text m-0'>
            Loading run details...
          </p>
        </div>
      </div>
    );
  }

  if (error) {
    return (
      <div className=' bg-elevation-surface z-50 flex items-center justify-center'>
        <div className='text-center'>
          <p className='font-noto-sans text-sm text-text-danger mb-4'>
            Error: {error}
          </p>
          <Button variant='default' onClick={onBack}>
            Go Back
          </Button>
        </div>
      </div>
    );
  }

  return (
    <div className=' bg-elevation-surface z-50 overflow-auto rounded-lg'>
      <div className='min-h-full'>
        {/* Header row matching Figma design */}
        <div className='bg-elevation-surface-raised border-b border-elevation-surface-raised'>
          <div className='flex items-center justify-between px-6 py-4'>
            {/* Left section with chevron and run info */}
            <div className='flex items-center gap-3'>
              <button
                title='Back'
                onClick={onBack}
                className='p-0 hover:bg-background-neutral-hovered rounded-lg w-[38px] h-[38px]'
              >
                <ChevronUpIcon className='rotate-90 size-6 m-auto' />
              </button>
              <div className='flex flex-col gap-1'>
                <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                  Agent: {run.agent_name}
                </p>
                <p className='font-noto-sans font-semibold text-sm text-text'>
                  Run: {run.run_id}
                </p>
              </div>
            </div>
            <div className='flex flex-col gap-1'>
              <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                Total Tasks
              </p>
              <p className='font-noto-sans font-normal text-sm text-text'>
                {run.total_tasks}
              </p>
            </div>

            <div className='flex flex-col gap-1'>
              <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                Success Rate
              </p>
              <p className='font-noto-sans font-normal text-sm'>
                <span className='text-text-success'>{run.success_count}</span>
                <span className='text-text-disabled'>/</span>
                <span className='text-text-danger'>{run.failure_count}</span>
                <span className='text-text-disabled'>
                  {' '}
                  ({((run.success_count / run.total_tasks) * 100).toFixed(0)}
                  %)
                </span>
              </p>
            </div>

            <div className='flex flex-col gap-1'>
              <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                Timestamp
              </p>
              <p className='font-noto-sans font-normal text-sm text-text'>
                {new Date(run.timestamp_utc).toLocaleString()}
              </p>
            </div>
          </div>
        </div>

        {/* Task details content */}
        <div className='p-6'>
          <div className='space-y-6'>
            {taskDetails.map((task, index) => (
              <div
                key={task.task_id + index}
                className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded'
              >
                <div className='p-5 space-y-4'>
                  {/* Task info row */}
                  <div className='grid grid-cols-4 gap-6'>
                    <div className='flex flex-col gap-1.5'>
                      <p className='font-noto-sans font-normal text-sm text-text-disabled truncate overflow-hidden'>
                        Task ID
                      </p>
                      <p className='font-noto-sans font-normal text-sm text-text truncate'>
                        {task.task_id ||
                          `task_${index.toString().padStart(3, '0')}`}
                      </p>
                    </div>

                    <div className='flex flex-col gap-1.5'>
                      <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                        Trace ID
                      </p>
                      <p className='font-noto-sans font-normal text-sm text-text'>
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
                        Status
                      </p>
                      <StatusBadge status={task.status} />
                    </div>
                  </div>

                  {/* Divider */}
                  <div className='h-px bg-elevation-surface-overlay'></div>

                  {/* Performance Metrics */}
                  <div className='space-y-4'>
                    <p className='font-noto-sans font-normal text-base text-text-disabled'>
                      Performance Metrics
                    </p>
                    <div className='grid grid-cols-4 gap-6'>
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
                          {task.metrics?.resource_usage?.cpu_time_sec.toFixed(
                            2
                          )}
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

                    <div className='grid grid-cols-4 gap-6'>
                      <div className='flex flex-col gap-1.5'>
                        <p className='font-inter font-normal text-sm text-text-disabled'>
                          Total Tokens
                        </p>
                        <p className='font-inter font-normal text-sm text-text'>
                          {task.metrics?.token_counts?.total_tokens || '_'}
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

                  {/* Divider */}
                  {/* <div className='h-px bg-elevation-surface-overlay'></div> */}

                  {/* Custom Metrics */}
                  <div className='space-y-4'>
                    <p className='font-noto-sans font-normal text-base text-text-disabled'>
                      Custom Metrics
                    </p>

                    <div className='grid grid-cols-4 gap-6'>
                      {task.metrics?.custom &&
                        Object.entries(task.metrics.custom).map(
                          ([key, value]) => (
                            <div key={key} className='flex flex-col gap-1.5'>
                              <p className='font-inter font-normal text-sm text-text-disabled'>
                                {key}
                              </p>
                              <p className='font-inter font-normal text-sm text-text'>
                                {String(value)}
                              </p>
                            </div>
                          )
                        )}
                    </div>
                  </div>

                  {/* Divider */}
                  <div className='h-px bg-elevation-surface-overlay'></div>

                  {/* Task Result */}
                  <div className='space-y-4'>
                    <button
                      onClick={() => toggleResultExpansion(task.task_id)}
                      className='flex items-center gap-2 font-inter font-normal text-sm text-text-disabled hover:text-text transition-colors'
                    >
                      <ChevronUpIcon
                        className={`size-4 transition-transform ${
                          expandedResults.has(task.task_id) ? 'rotate-180' : ''
                        }`}
                      />
                      Task Result
                      {expandedResults.has(task.task_id) ? ' (Full JSON)' : ''}
                    </button>
                    <div className='bg-elevation-surface-sunken rounded p-4 h-fit overflow-auto'>
                      <pre className='font-inter font-normal text-sm text-text whitespace-pre-wrap'>
                        {expandedResults.has(task.task_id)
                          ? task.results
                            ? JSON.stringify(task.results, null, 2)
                            : 'No results available.'
                          : task.results?.side_effects?.doc_interaction
                            ? typeof task.results.side_effects.doc_interaction === 'string'
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

                  {/* View Logs Button */}
                  <Button variant='default' onClick={() => openCodeModal(task)}>
                    View Logs
                  </Button>
                </div>
              </div>
            ))}
          </div>
        </div>
      </div>
    </div>
  );
};

export default RunDetailsView;
