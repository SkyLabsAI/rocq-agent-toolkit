'use client';

import { useSearchParams } from 'next/navigation';
import React from 'react';

import TaskSetDetailsPage from '@/features/project-details';

const TaskSetPage = () => {
  const searchParams = useSearchParams();
  const id = searchParams.get('id');

  if (!id) {
    return <div>No taskset ID provided</div>;
  }

  return <TaskSetDetailsPage tasksetId={id} />;
};

export default TaskSetPage;
