'use client';

import { use } from 'react';

import RunDetailsPage from '@/features/run-details';

const RunPage = ({ params }: { params: Promise<{ runId: string }> }) => {
  const { runId } = use(params);

  if (!runId) {
    return <div>No run ID provided</div>;
  }

  return <RunDetailsPage runId={runId} />;
};

export default RunPage;
