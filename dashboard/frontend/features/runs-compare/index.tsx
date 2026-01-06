'use client';

import React, { Suspense } from 'react';

import Layout from '@/layouts/common';
import type { RunDetailsResponse, TaskOutput } from '@/types/types';

import { ComparePageContent } from './compare-page-content';

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

interface ComparePageProps {
  runIds: string[];
}

const ComparePage: React.FC<ComparePageProps> = ({ runIds }) => {
  return (
    <Layout title='Compare Runs'>
      <div className='  text-text p-8 pt-0'>
        <div className='max-w-7xl mx-auto space-y-8'></div>
        <Suspense
          fallback={
            <div className='min-h-screen  text-text p-8'>
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
          <ComparePageContent runIds={runIds} />
        </Suspense>
      </div>
    </Layout>
  );
};

export default ComparePage;
