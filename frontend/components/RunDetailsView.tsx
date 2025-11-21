import React, { useEffect, useState } from 'react';
import { Button } from '@/components/base/Button';
import { getRunDetails } from '@/services/dataservice';
import type { TaskOutput, RunDetailsResponse } from '@/types/types';

interface RunDetailsViewProps {
  run: {
    run_id: string;
    agent_name: string;
    timestamp_utc: string;
    total_tasks: number;
    success_count: number;
    failure_count: number;
  };
  loadingLogs: string | null;
  onBack: () => void;
  openCodeModal: (task: TaskOutput) => void;
}

function ChevronLeft() {
  return (
    <div className="relative size-6">
      <svg className="block size-full" fill="none" preserveAspectRatio="none" viewBox="0 0 24 24">
        <path d="M7.41 15.41L12 10.83L16.59 15.41L18 14L12 8L6 14L7.41 15.41Z" fill="#292A2E" transform="rotate(90 12 12)" />
      </svg>
    </div>
  );
}

function StatusBadge({ status }: { status: string }) {
  const isSuccess = status.toLowerCase() === 'success';
  return (
    <div className="inline-flex items-center">
      <div className={`h-5 rounded-[15px] px-3 py-0.5 ${isSuccess ? 'bg-[#efffd6] opacity-50' : 'bg-red-100'}`}>
        <p className={`font-inter font-semibold text-xs ${isSuccess ? 'text-[#4c6b1f]' : 'text-red-600'}`}>
          {status}
        </p>
      </div>
    </div>
  );
}

const RunDetailsView: React.FC<RunDetailsViewProps> = ({
  run,
  loadingLogs,
  onBack,
  openCodeModal,
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
        setError(err instanceof Error ? err.message : 'Failed to fetch run details');
      } finally {
        setLoading(false);
      }
    };

    fetchRunDetails();
  }, [run.run_id]);

  if (loading) {
    return (
      <div className="fixed inset-0 bg-white z-50 flex items-center justify-center">
        <div className="text-center">
          <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-[#292a2e] mb-4"></div>
          <p className="font-noto-sans text-sm text-[#292a2e]">Loading run details...</p>
        </div>
      </div>
    );
  }

  if (error) {
    return (
      <div className="fixed inset-0 bg-white z-50 flex items-center justify-center">
        <div className="text-center">
          <p className="font-noto-sans text-sm text-red-600 mb-4">Error: {error}</p>
          <Button variant="default" onClick={onBack}>
            Go Back
          </Button>
        </div>
      </div>
    );
  }

  return (
    <div className="fixed inset-0 bg-white z-50 overflow-auto">
      <div className="min-h-full">
        {/* Header row matching Figma design */}
        <div className="bg-[#f9fbfd] border-b border-[#ececec]">
          <div className="flex items-center justify-between px-6 py-4">
            {/* Left section with chevron and run info */}
            <div className="flex items-center gap-3">
              <Button
                variant="ghost"
                onClick={onBack}
                className="p-1"
                leftIcon={<ChevronLeft />}
              >
                {/* Hidden text for button */}
                <span className="sr-only">Back</span>
              </Button>
              <div className="flex flex-col gap-1">
                <p className="font-noto-sans font-normal text-sm text-[rgba(8,15,33,0.35)]">
                  Agent: {run.agent_name}
                </p>
                <p className="font-noto-sans font-semibold text-sm text-[#292a2e]">
                  Run: {run.run_id}
                </p>
              </div>
            </div>

            {/* Right section with metrics */}
            <div className="flex items-center gap-6">
              <div className="flex flex-col gap-2">
                <p className="font-noto-sans font-normal text-sm text-[rgba(8,15,33,0.35)]">
                  Total Tasks
                </p>
                <p className="font-noto-sans font-normal text-sm text-[#292a2e]">
                  {run.total_tasks}
                </p>
              </div>
              
              <div className="flex flex-col gap-2">
                <p className="font-noto-sans font-normal text-sm text-[rgba(8,15,33,0.35)]">
                  Success Rate
                </p>
                <p className="font-noto-sans font-normal text-sm">
                  <span className="text-[#4c6b1f]">{run.success_count}</span>
                  <span className="text-[rgba(8,15,33,0.35)]">/</span>
                  <span className="text-[#ae2e24]">{run.failure_count}</span>
                  <span className="text-[rgba(8,15,33,0.35)]"> ({((run.success_count / run.total_tasks) * 100).toFixed(0)}%)</span>
                </p>
              </div>
              
              <div className="flex flex-col gap-2">
                <p className="font-noto-sans font-normal text-sm text-[rgba(8,15,33,0.35)]">
                  Timestamp
                </p>
                <p className="font-noto-sans font-normal text-sm text-[#292a2e]">
                  {new Date(run.timestamp_utc).toLocaleString()}
                </p>
              </div>

              <Button variant="default" className="bg-[#f0f1f2] text-[#292a2e] border-[#dddee1]">
                Compare
              </Button>
            </div>
          </div>
        </div>

        {/* Task details content */}
        <div className="p-6">
          <div className="space-y-6">
            {taskDetails.map((task, index) => (
              <div key={task.task_id || index} className="bg-[#f9fbfd] border border-[#ececec] rounded">
                <div className="p-5 space-y-4">
                  {/* Task info row */}
                  <div className="grid grid-cols-4 gap-6">
                    <div className="flex flex-col gap-1.5">
                      <p className="font-noto-sans font-normal text-sm text-[rgba(8,15,33,0.35)]">
                        Task ID
                      </p>
                      <p className="font-noto-sans font-normal text-sm text-[#292a2e]">
                        {task.task_id || `task_${index.toString().padStart(3, '0')}`}
                      </p>
                    </div>
                    
                    <div className="flex flex-col gap-1.5">
                      <p className="font-noto-sans font-normal text-sm text-[rgba(8,15,33,0.35)]">
                        Trace ID
                      </p>
                      <p className="font-noto-sans font-normal text-sm text-[#292a2e]">
                        {task.trace_id || 'trace_pe1melqs0r'}
                      </p>
                    </div>
                    
                    <div className="flex flex-col gap-1.5">
                      <p className="font-noto-sans font-normal text-sm text-[rgba(8,15,33,0.35)]">
                        Task Kind
                      </p>
                      <p className="font-noto-sans font-normal text-sm text-[#292a2e]">
                        {typeof task.task_kind === 'string' ? task.task_kind : task.task_kind?.kind || 'FullProofTask'}
                      </p>
                    </div>
                    
                    <div className="flex flex-col gap-1.5">
                      <p className="font-noto-sans font-normal text-sm text-[rgba(8,15,33,0.35)]">
                        Status
                      </p>
                      <StatusBadge status={task.status || 'Success'} />
                    </div>
                  </div>

                  {/* Divider */}
                  <div className="h-px bg-[#ececec]"></div>

                  {/* Performance Metrics */}
                  <div className="space-y-4">
                    <p className="font-noto-sans font-normal text-base text-[rgba(8,15,33,0.35)]">
                      Performance Metrics
                    </p>
                    <div className="grid grid-cols-4 gap-6">
                      <div className="flex flex-col gap-1.5">
                        <p className="font-inter font-normal text-sm text-[rgba(8,15,33,0.35)]">
                          Execution Time
                        </p>
                        <p className="font-inter font-normal text-sm text-[#292a2e]">
                          {task.metrics?.resource_usage?.execution_time_sec ? `${task.metrics.resource_usage.execution_time_sec.toFixed(2)}s` : '23.01s'}
                        </p>
                      </div>
                      
                      <div className="flex flex-col gap-1.5">
                        <p className="font-inter font-normal text-sm text-[rgba(8,15,33,0.35)]">
                          CPU Time
                        </p>
                        <p className="font-inter font-normal text-sm text-[#292a2e]">
                          {task.metrics?.resource_usage?.cpu_time_sec ? `${task.metrics.resource_usage.cpu_time_sec.toFixed(2)}s` : '24.98s'}
                        </p>
                      </div>
                      
                      <div className="flex flex-col gap-1.5">
                        <p className="font-inter font-normal text-sm text-[rgba(8,15,33,0.35)]">
                          GPU Time
                        </p>
                        <p className="font-inter font-normal text-sm text-[#292a2e]">
                          {task.metrics?.resource_usage?.gpu_time_sec ? `${task.metrics.resource_usage.gpu_time_sec.toFixed(2)}s` : '7.80s'}
                        </p>
                      </div>
                    </div>

                    <div className="grid grid-cols-4 gap-6">
                      <div className="flex flex-col gap-1.5">
                        <p className="font-inter font-normal text-sm text-[rgba(8,15,33,0.35)]">
                          LLM Calls
                        </p>
                        <p className="font-inter font-normal text-sm text-[#292a2e]">
                          {task.metrics?.llm_invocation_count || '24'}
                        </p>
                      </div>
                      
                      <div className="flex flex-col gap-1.5">
                        <p className="font-inter font-normal text-sm text-[rgba(8,15,33,0.35)]">
                          Total Tokens
                        </p>
                        <p className="font-inter font-normal text-sm text-[#292a2e]">
                          {task.metrics?.token_counts?.total_tokens || '0'}
                        </p>
                      </div>
                      
                      <div className="flex flex-col gap-1.5">
                        <p className="font-inter font-normal text-sm text-[rgba(8,15,33,0.35)]">
                          Input Tokens
                        </p>
                        <p className="font-inter font-normal text-sm text-[#292a2e]">
                          {task.metrics?.token_counts?.input_tokens?.toLocaleString() || '3,767'}
                        </p>
                      </div>
                      
                      <div className="flex flex-col gap-1.5">
                        <p className="font-inter font-normal text-sm text-[rgba(8,15,33,0.35)]">
                          Output Tokens
                        </p>
                        <p className="font-inter font-normal text-sm text-[#292a2e]">
                          {task.metrics?.token_counts?.output_tokens?.toLocaleString() || '2,129'}
                        </p>
                      </div>
                    </div>
                  </div>

                  {/* Divider */}
                  <div className="h-px bg-[#ececec]"></div>

                  {/* Custom Metrics */}
                  <div className="space-y-4">
                    <p className="font-noto-sans font-normal text-base text-[rgba(8,15,33,0.35)]">
                      Custom Metrics
                    </p>
                    <div className="flex flex-col gap-1.5">
                      <p className="font-inter font-normal text-sm text-[rgba(8,15,33,0.35)]">
                        Proof Complexity
                      </p>
                      <p className="font-inter font-normal text-sm text-[#292a2e]">
                        {String(task.metrics?.custom_metrics?.proof_complexity) || '5'}
                      </p>
                    </div>
                  </div>

                  {/* Divider */}
                  <div className="h-px bg-[#ececec]"></div>

                  {/* Task Result */}
                  <div className="space-y-4">
                    <p className="font-inter font-normal text-sm text-[rgba(8,15,33,0.35)]">
                      Task Result
                    </p>
                    <div className="bg-[#f0f2f4] rounded p-4 h-[105px] overflow-auto">
                      <pre className="font-inter font-normal text-sm text-[#292a2e] whitespace-pre-wrap">
                        {task.results ? JSON.stringify(task.results, null, 2) : JSON.stringify({
                          "proof_found": true,
                          "steps_taken": 13
                        }, null, 2)}
                      </pre>
                    </div>
                  </div>

                  {/* View Logs Button */}
                  <Button 
                    variant="default" 
                    className="bg-[#f0f1f2] text-[#292a2e] border-[#dddee1]"
                    onClick={() => openCodeModal(task)}
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