'use client';

import { use } from 'react';

import TaskDetailsPageContent from '@/features/task-details-page';

const TaskDetailsPage = ({
  params,
}: {
  params: Promise<{ runId: string; taskid: string }>;
}) => {
  const { runId, taskid } = use(params);
  return <TaskDetailsPageContent runId={runId} taskId={taskid} />;
};

export default TaskDetailsPage;
