'use client';

import { useSearchParams } from 'next/navigation';
import { use } from 'react';

import TaskDetailsPageContent from '@/features/task-details-page';

const TaskDetailsPage = ({
  params,
}: {
  params: Promise<{ runId: string }>;
}) => {
  const { runId } = use(params);
  const searchParams = useSearchParams();
  const taskId = searchParams.get('taskId');

  if (!taskId) {
    return (
      <div className='flex items-center justify-center min-h-screen bg-elevation-surface'>
        <div className='text-center'>
          <p className='font-noto-sans text-sm text-text-danger mb-4'>
            Task ID is required
          </p>
        </div>
      </div>
    );
  }

  return <TaskDetailsPageContent runId={runId} taskId={taskId} />;
};

export default TaskDetailsPage;
