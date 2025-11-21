import React, { useEffect, useState } from 'react';
import { Button } from '@/components/base/Button';
import { getRunDetails } from '@/services/dataservice';
import type { TaskOutput, RunDetailsResponse } from '@/types/types';
import { ChevronDownIcon } from '@/icons/chevron-up';
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

}





const RunDetailsView: React.FC<RunDetailsViewProps> = ({
  run,
  onBack,

}) => {
  const [taskDetails, setTaskDetails] = useState<TaskOutput[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

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
        console.error('Error fetching run details:', err);
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
      <div className=' bg-white z-50 flex items-center justify-center'>
        <div className='text-center'>
          <div className='animate-spin rounded-full h-12 w-12 border-b-2 border-[#292a2e] mb-4'></div>
          <p className='font-noto-sans text-sm text-[#292a2e]'>
            Loading run details...
          </p>
        </div>
      </div>
    );
  }

  if (error) {
    return (
      <div className=' bg-white z-50 flex items-center justify-center'>
        <div className='text-center'>
          <p className='font-noto-sans text-sm text-red-600 mb-4'>
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
              <Button variant='ghost' onClick={onBack} className='p-1'>
                <ChevronDownIcon />
              </Button>
              <div className='flex flex-col gap-1'>
                <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                  Agent: {run.agent_name}
                </p>
                <p className='font-noto-sans font-semibold text-sm text-text'>
                  Run: {run.run_id}
                </p>
              </div>
            </div>

            {/* Right section with metrics */}
           
              <div className='flex flex-col gap-2'>
                <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                  Total Tasks
                </p>
                <p className='font-noto-sans font-normal text-sm text-text'>
                  {run.total_tasks}
                </p>
              </div>

              <div className='flex flex-col gap-2'>
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

              <div className='flex flex-col gap-2'>
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
                key={task.task_id || index}
                className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded'
              >
                <div className='p-5 space-y-4'>
                  {/* Task info row */}
                  <div className='grid grid-cols-4 gap-6'>
                    <div className='flex flex-col gap-1.5'>
                      <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                        Task ID
                      </p>
                      <p className='font-noto-sans font-normal text-sm text-text'>
                        {task.task_id ||
                          `task_${index.toString().padStart(3, '0')}`}
                      </p>
                    </div>

                    <div className='flex flex-col gap-1.5'>
                      <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                        Trace ID
                      </p>
                      <p className='font-noto-sans font-normal text-sm text-text'>
                        {task.trace_id || 'trace_pe1melqs0r'}
                      </p>
                    </div>

                    <div className='flex flex-col gap-1.5'>
                      <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                        Task Kind
                      </p>
                      <p className='font-noto-sans font-normal text-sm text-text'>
                        {typeof task.task_kind === 'string'
                          ? task.task_kind
                          : task.task_kind?.kind || 'FullProofTask'}
                      </p>
                    </div>

                    <div className='flex flex-col gap-1.5'>
                      <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                        Status
                      </p>
                      <StatusBadge status={task.status || 'Success'} />
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
                          {task.metrics?.resource_usage?.execution_time_sec
                            ? `${task.metrics.resource_usage.execution_time_sec.toFixed(2)}s`
                            : '23.01s'}
                        </p>
                      </div>

                      <div className='flex flex-col gap-1.5'>
                        <p className='font-inter font-normal text-sm text-text-disabled'>
                          CPU Time
                        </p>
                        <p className='font-inter font-normal text-sm text-text'>
                          {task.metrics?.resource_usage?.cpu_time_sec
                            ? `${task.metrics.resource_usage.cpu_time_sec.toFixed(2)}s`
                            : '24.98s'}
                        </p>
                      </div>

                      <div className='flex flex-col gap-1.5'>
                        <p className='font-inter font-normal text-sm text-text-disabled'>
                          GPU Time
                        </p>
                        <p className='font-inter font-normal text-sm text-text'>
                          {task.metrics?.resource_usage?.gpu_time_sec
                            ? `${task.metrics.resource_usage.gpu_time_sec.toFixed(2)}s`
                            : '7.80s'}
                        </p>
                      </div>
                    </div>

                    <div className='grid grid-cols-4 gap-6'>
                      <div className='flex flex-col gap-1.5'>
                        <p className='font-inter font-normal text-sm text-text-disabled'>
                          LLM Calls
                        </p>
                        <p className='font-inter font-normal text-sm text-text'>
                          {task.metrics?.llm_invocation_count || '24'}
                        </p>
                      </div>

                      <div className='flex flex-col gap-1.5'>
                        <p className='font-inter font-normal text-sm text-text-disabled'>
                          Total Tokens
                        </p>
                        <p className='font-inter font-normal text-sm text-text'>
                          {task.metrics?.token_counts?.total_tokens || '0'}
                        </p>
                      </div>

                      <div className='flex flex-col gap-1.5'>
                        <p className='font-inter font-normal text-sm text-text-disabled'>
                          Input Tokens
                        </p>
                        <p className='font-inter font-normal text-sm text-text'>
                          {task.metrics?.token_counts?.input_tokens?.toLocaleString() ||
                            '3,767'}
                        </p>
                      </div>

                      <div className='flex flex-col gap-1.5'>
                        <p className='font-inter font-normal text-sm text-text-disabled'>
                          Output Tokens
                        </p>
                        <p className='font-inter font-normal text-sm text-text'>
                          {task.metrics?.token_counts?.output_tokens?.toLocaleString() ||
                            '2,129'}
                        </p>
                      </div>
                    </div>
                  </div>

                  {/* Divider */}
                  <div className='h-px bg-elevation-surface-overlay'></div>

                  {/* Custom Metrics */}
                  <div className='space-y-4'>
                    <p className='font-noto-sans font-normal text-base text-text-disabled'>
                      Custom Metrics
                    </p>
                    <div className='flex flex-col gap-1.5'>
                      <p className='font-inter font-normal text-sm text-text-disabled'>
                        Proof Complexity
                      </p>
                      <p className='font-inter font-normal text-sm text-text'>
                        {String(
                          task.metrics?.custom_metrics?.proof_complexity
                        ) || '5'}
                      </p>
                    </div>
                  </div>

                  {/* Divider */}
                  <div className='h-px bg-elevation-surface-overlay'></div>

                  {/* Task Result */}
                  <div className='space-y-4'>
                    <p className='font-inter font-normal text-sm text-text-disabled'>
                      Task Result
                    </p>
                    <div className='bg-elevation-surface-sunken rounded p-4 h-fit overflow-auto'>
                      <pre className='font-inter font-normal text-sm text-text whitespace-pre-wrap'>
                        {task.results
                          ? JSON.stringify(task.results, null, 2)
                          : JSON.stringify(
                              {
                                proof_found: true,
                                steps_taken: 13,
                              },
                              null,
                              2
                            )}
                      </pre>
                    </div>
                  </div>

                  {/* View Logs Button */}
                  <Button
                    variant='default'
                    // onClick={() => openCodeModal(task)}
                  >
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
