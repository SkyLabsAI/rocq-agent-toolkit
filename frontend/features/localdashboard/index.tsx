'use client';

import React from 'react';
import Layout from '@/layouts/common';
import { useLocalDashboard } from '@/hooks/useLocalDashboard';
import AgentTable from './AgentTable';

const LocalDashboard: React.FC = () => {
  const {
    isRefreshing,
    refreshMessage,
    handleRefresh,
  } = useLocalDashboard();
  

  return (
    <Layout title='Internal Dashboard'>
      {/* Refresh Message */}
      {refreshMessage && (
        <div className='mb-4 bg-elevation-surface-raised backdrop-blur-sm border border-elevation-surface-overlay rounded-xl p-4'>
          <p className='text-sm text-green-400'>{refreshMessage}</p>
        </div>
      )}
      {/* Main Table - only show when no run details are selected */}

        <AgentTable
          isRefreshing={isRefreshing}
          handleRefresh={handleRefresh}
         />
    
     
    </Layout>
  );
};

export default LocalDashboard;
