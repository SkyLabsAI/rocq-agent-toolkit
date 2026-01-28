'use client';

import React from 'react';

import LatestRunsList from '@/components/latest-runs-list';
import Layout from '@/layouts/common';

import AgentTable from './agent-table';

const LocalDashboard: React.FC = () => {
  return (
    <Layout title='Internal Dashboard'>
      {/* Latest Runs List */}
      <LatestRunsList />

      {/* Main Table - only show when no run details are selected */}
      <AgentTable />
    </Layout>
  );
};

export default LocalDashboard;
