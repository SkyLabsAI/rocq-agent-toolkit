'use client';

import React from 'react';

import Layout from '@/layouts/common';

import AgentTable from './AgentTable';

const LocalDashboard: React.FC = () => {
  return (
    <Layout title='Internal Dashboard'>
      {/* Refresh Message */}

      {/* Main Table - only show when no run details are selected */}

      <AgentTable />
    </Layout>
  );
};

export default LocalDashboard;
