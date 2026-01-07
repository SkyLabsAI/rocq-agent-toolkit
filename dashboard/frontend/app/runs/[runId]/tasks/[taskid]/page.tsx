'use client';

import { use } from 'react';

import TaskDetailsPageContent from '@/features/task-details-page';
import Layout from '@/layouts/common';

const TaskDetailsPage = ({
  params,
}: {
  params: Promise<{ runId: string; taskid: string }>;
}) => {
  const { runId, taskid } = use(params);
  return (
    <Layout title='Task Details'>
      <TaskDetailsPageContent runId={runId} taskId={taskid} />
    </Layout>
  );
};

export default TaskDetailsPage;
