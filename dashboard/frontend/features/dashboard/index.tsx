'use client';

import React from 'react';

import Layout from '@/layouts/common';

import AgentTable from './agent-table';

const Dashboard: React.FC = () => {
  return (
    <Layout title='RAT Dashboard'>
      {/* Refresh Message */}

      {/* Main Table - only show when no run details are selected */}

      <AgentTable />
    </Layout>
  );
};

export default Dashboard;
