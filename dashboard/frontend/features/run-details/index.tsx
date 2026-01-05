'use client';

import { useRouter, useSearchParams } from 'next/navigation';
import React, { useEffect, useState } from 'react';

import RunDetailsView from '@/components/run-details-view';
import TaskDetailsModal from '@/features/task-details-modal';
import { getRunDetails } from '@/services/dataservice';
import type { RunDetailsResponse, TaskOutput } from '@/types/types';

interface ModalState {
  isOpen: boolean;
  logs: Record<string, unknown> | null;
  selectedTask: TaskOutput | null;
}

interface RunDetailsPageProps {
  runId: string;
}

const RunDetailsPage: React.FC<RunDetailsPageProps> = ({ runId }) => {
  const router = useRouter();
  const searchParams = useSearchParams();
  const [runData, setRunData] = useState<RunDetailsResponse | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  const [modalState, setModalState] = useState<ModalState>({
    isOpen: false,
    logs: null,
    selectedTask: null,
  });

  // Parse tags from URL query parameters
  const initialSelectedTags = searchParams.get('tags')
    ? searchParams.get('tags')!.split(',').filter(Boolean)
    : [];

  // Parse status from URL query parameters
  const initialStatusFilter = (() => {
    const status = searchParams.get('status');
    if (status === 'Success' || status === 'Failure') {
      return status;
    }
    return 'all';
  })();

  // Parse task ID filter from URL query parameters
  const initialTaskIdFilter = searchParams.get('taskId') || '';

  useEffect(() => {
    const fetchRunDetails = async () => {
      setLoading(true);
      setError(null);

      try {
        const details = await getRunDetails([runId]);
        if (details.length > 0) {
          setRunData(details[0]);
        } else {
          setError('Run not found');
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
  }, [runId]);

  const openCodeModal = (task: TaskOutput) => {
    setModalState({
      isOpen: true,
      logs: null,
      selectedTask: task,
    });
  };

  const closeModal = () => {
    setModalState({
      isOpen: false,
      logs: null,
      selectedTask: null,
    });
  };

  const handleBack = () => {
    router.push('/');
  };

  if (loading) {
    return (
      <div className='flex items-center justify-center min-h-screen bg-elevation-surface'>
        <div className='text-center flex flex-col gap-5 justify-center items-center'>
          <div className='animate-spin rounded-full h-12 w-12 border-b-2 border-elevation-surface-overlay'></div>
          <p className='font-noto-sans text-sm text-text m-0'>
            Loading run details...
          </p>
        </div>
      </div>
    );
  }

  if (error || !runData) {
    return (
      <div className='flex items-center justify-center min-h-screen bg-elevation-surface'>
        <div className='text-center'>
          <p className='font-noto-sans text-sm text-text-danger mb-4'>
            Error: {error || 'Run not found'}
          </p>
          <button
            className='px-4 py-2 bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg text-text hover:bg-elevation-surface-overlay transition-colors'
            onClick={handleBack}
          >
            Go Back to Dashboard
          </button>
        </div>
      </div>
    );
  }

  // Transform RunDetailsResponse to match RunDetailsView's expected format
  const runViewData = {
    run_id: runData.run_id,
    agent_name: runData.agent_name,
    timestamp_utc:
      (runData.metadata?.timestamp_utc as string) || new Date().toISOString(),
    total_tasks: runData.total_tasks,
    success_count: runData.tasks.filter(t => t.status === 'Success').length,
    failure_count: runData.tasks.filter(t => t.status === 'Failure').length,
  };

  return (
    <div className='min-h-screen bg-elevation-surface p-6'>
      <RunDetailsView
        run={runViewData}
        onBack={handleBack}
        openCodeModal={openCodeModal}
        initialSelectedTags={initialSelectedTags}
        initialStatusFilter={initialStatusFilter}
        initialTaskIdFilter={initialTaskIdFilter}
        runId={runId}
      />

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
    </div>
  );
};

export default RunDetailsPage;
