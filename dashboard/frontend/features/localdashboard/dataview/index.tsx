import React from 'react';
import { useBenchmarks } from '../../../hooks/use-dataview';
import { DataItem } from './data-item';
import { GlobalCompareProvider } from '@/contexts/GlobalCompareContext';
import { GlobalStickyCompareBar } from '@/components/GlobalStickyCompareBar';

const DataView: React.FC = ({}) => {
  const { benchmarks} = useBenchmarks();

  return (
    <GlobalCompareProvider>
      <div className='flex flex-col gap-4'>
        {benchmarks.map((benchmark) => (
          <DataItem key={benchmark.dataset_id} benchmark={benchmark} />
        ))}
      </div>
      <GlobalStickyCompareBar />
    </GlobalCompareProvider>
  );
};

export default DataView;
