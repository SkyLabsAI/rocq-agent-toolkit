'use client';

import { use } from 'react';

import TaskSetDetailsPage from '@/features/project-details';

const TaskSetPage = ({ params }: { params: Promise<{ id: string }> }) => {
  const { id } = use(params);

  if (!id) {
    return <div>No taskset ID provided</div>;
  }

  return <TaskSetDetailsPage tasksetId={id} />;
};

export default TaskSetPage;
