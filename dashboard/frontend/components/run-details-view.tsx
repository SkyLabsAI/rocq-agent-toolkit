import { useRouter } from 'next/navigation';
import React, { useEffect, useState } from 'react';

import { ChevronUpIcon } from '@/icons/chevron-up';
import { getRunDetails } from '@/services/dataservice';
import type { TaskOutput } from '@/types/types';

import TaskDetailsPanel from './task-details-panel';
import TasksTable from './tasks-table';

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
  initialSelectedTags?: string[];
  runId: string;
}

const RunDetailsView: React.FC<RunDetailsViewProps> = ({
  run,
  onBack,
  openCodeModal,
  initialSelectedTags = [],
  runId,
}) => {
  const router = useRouter();
  const [taskDetails, setTaskDetails] = useState<TaskOutput[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [selectedTask, setSelectedTask] = useState<TaskOutput | null>(null);
  const [isPanelOpen, setIsPanelOpen] = useState(false);
  const [selectedTags, setSelectedTags] =
    useState<string[]>(initialSelectedTags);

  // Update URL when tags change
  useEffect(() => {
    const params = new URLSearchParams();
    if (selectedTags.length > 0) {
      params.set('tags', selectedTags.join(','));
    }
    const queryString = params.toString();
    const newUrl = queryString
      ? `/runs/${runId}?${queryString}`
      : `/runs/${runId}`;
    router.replace(newUrl, { scroll: false });
  }, [selectedTags, runId, router]);

  const handleTaskClick = (task: TaskOutput) => {
    setSelectedTask(task);
    setIsPanelOpen(true);
  };

  const handlePanelClose = () => {
    setIsPanelOpen(false);
    // Wait for animation to complete before clearing selected task
    setTimeout(() => setSelectedTask(null), 300);
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
          <button
            className='px-4 py-2 bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg text-text hover:bg-elevation-surface-overlay transition-colors'
            onClick={onBack}
          >
            Go Back
          </button>
        </div>
      </div>
    );
  }

  return (
    <>
      <div className='bg-elevation-surface z-30 overflow-auto rounded-lg'>
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

          {/* Task table content */}
          <div className='p-6'>
            <TasksTable
              tasks={taskDetails}
              onTaskClick={handleTaskClick}
              initialSelectedTags={selectedTags}
              onTagsChange={setSelectedTags}
            />
          </div>
        </div>
      </div>

      {/* Slide-out Task Details Panel */}
      <TaskDetailsPanel
        task={selectedTask}
        isOpen={isPanelOpen}
        onClose={handlePanelClose}
        openCodeModal={openCodeModal}
      />
    </>
  );
};

export default RunDetailsView;
