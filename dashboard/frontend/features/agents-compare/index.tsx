import React, { Suspense } from 'react';

import Layout from '@/layouts/common';

import { AgentCompareContent } from './agent-compare-content';

interface AgentCompareTableProps {
  agentIds: string[];
}

const AgentCompareTable: React.FC<AgentCompareTableProps> = ({ agentIds }) => {
  return (
    <Layout title='Compare Agents'>
      <div className='text-text p-8 pt-0'>
        <div className='max-w-7xl mx-auto space-y-8'></div>
        <Suspense
          fallback={
            <div className='min-h-screen text-text p-8'>
              <div className='max-w-7xl mx-auto'>
                <div className='flex items-center justify-center h-64'>
                  <div className='text-text-disabled'>
                    Loading comparison data...
                  </div>
                </div>
              </div>
            </div>
          }
        >
          <AgentCompareContent agentIds={agentIds} />
        </Suspense>
      </div>
    </Layout>
  );
};

export default AgentCompareTable;
