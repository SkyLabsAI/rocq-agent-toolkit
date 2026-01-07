'use client';

import { use } from 'react';

import RunDetailsPage from '@/features/run-details';
import Layout from '@/layouts/common';

const RunPage = ({ params }: { params: Promise<{ runId: string }> }) => {
  const { runId } = use(params);

  if (!runId) {
    return <div>No run ID provided</div>;
  }

  return (
    <Layout title='Run Details'>
      <RunDetailsPage runId={runId} />
    </Layout>
  );
};

export default RunPage;
