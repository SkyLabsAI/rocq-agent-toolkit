'use client';

import React, { Suspense } from 'react';
import type { TaskOutput, RunDetailsResponse } from '@/types/types';
import { ComparePageContent } from './compare-page-content';
import Layout from '@/layouts/common';

export interface RunStats {
  id: string;
  name: string;
  tasks: number;
  successRate: number;
  totalLlmCalls: number;
  totalTokens: number;
  avgExecutionTime: number;
}

export interface RunTaskCell {
  run: RunDetailsResponse;
  task?: TaskOutput;
}

const ComparePage: React.FC = () => {
  return (
    <Layout title='Compare Runs'>
      <div className='  text-white p-8'>
        <div className='max-w-7xl mx-auto space-y-8'></div>
        <Suspense
          fallback={
            <div className='min-h-screen  text-white p-8'>
              <div className='max-w-7xl mx-auto'>
                <div className='flex items-center justify-center h-64'>
                  <div className='text-gray-400'>
                    Loading comparison data...
                  </div>
                </div>
              </div>
            </div>
          }
        >
          <ComparePageContent />
        </Suspense>
      </div>
    </Layout>
  );
};

export default ComparePage;

