import React from 'react';

import { GlobalStickyCompareBar } from '@/components/global-sticky-compare-bar';
import { GlobalCompareProvider } from '@/contexts/global-compare-context';

import { useBenchmarks } from '../../../hooks/use-dataview';
import { DataItem } from './data-item';

const DataView: React.FC = () => {
  const { benchmarks } = useBenchmarks();

  return (
    <GlobalCompareProvider>
      <div className='flex flex-col gap-4' data-testid='datasets-view'>
        {benchmarks.map((benchmark, index) => (
          <DataItem
            key={benchmark.dataset_id}
            benchmark={benchmark}
            index={index}
          />
        ))}
      </div>
      <GlobalStickyCompareBar />
    </GlobalCompareProvider>
  );
};

export default DataView;
