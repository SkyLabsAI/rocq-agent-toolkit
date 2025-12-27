import { useState } from 'react';
import { useNavigate } from 'react-router-dom';

import { useGlobalCompare } from '@/contexts/global-compare-context';
import AgentRunsView from '@/features/localdashboard/agent-runs-view';
import { ChevronUpIcon } from '@/icons/chevron-up';
import { type Benchmark, type Run } from '@/types/types';
import { cn } from '@/utils/cn';

import { useInstanceBenchmarks } from './use-instance-benchmarks';

interface InstanceBenchmarksProps {
  benchmark: Benchmark;
  instanceChecksum: string;
  instanceName: string;
}

export const InstanceBenchmarks: React.FC<InstanceBenchmarksProps> = ({
  benchmark,
  instanceChecksum,
  instanceName,
}) => {
  const [isOpen, setIsOpen] = useState(false);
  const { runs, isLoading, fetchRuns } = useInstanceBenchmarks(
    instanceChecksum,
    benchmark.dataset_id
  );
  const navigate = useNavigate();

  const {
    selectRun,
    deselectRun,
    getSelectedRunsForDataset,
    isRunSelected,
    clearDatasetSelections,
  } = useGlobalCompare();

  const handleToggle = () => {
    const newIsOpen = !isOpen;
    setIsOpen(newIsOpen);
    if (newIsOpen && runs.length === 0) {
      fetchRuns();
    }
  };

  const toggleRunSelection = (run: Run) => {
    if (isRunSelected(run.run_id, benchmark.dataset_id)) {
      deselectRun(run.run_id, benchmark.dataset_id);
    } else {
      selectRun(run.run_id, benchmark.dataset_id);
    }
  };

  const compareSelected = () => {
    const selectedRunIds = getSelectedRunsForDataset(benchmark.dataset_id);
    if (selectedRunIds.length < 1) return;
    const query = new URLSearchParams({
      runs: selectedRunIds.join(','),
    }).toString();
    navigate({
      pathname: '/compare',
      search: `?${query}`,
    });
  };

  return (
    <div
      className='border-l-2 border-elevation-surface-overlay ml-6'
      data-testid={`instance-dataset-card-${benchmark.dataset_id}`}
    >
      <div
        className='bg-elevation-surface-raised hover:bg-white/5 overflow-hidden py-3 px-6 flex justify-between items-center cursor-pointer transition-colors'
        onClick={handleToggle}
      >
        <div className='flex gap-2 items-center text-text'>
          <ChevronUpIcon
            className={cn('size-4 text-text-disabled', {
              'rotate-180': isOpen,
            })}
          />
          <span className='text-[14px]' data-testid='dataset-name'>
            {benchmark.dataset_id}
          </span>
        </div>

        <span className='text-text-disabled text-xs'>{''}</span>
      </div>
      {isOpen &&
        (isLoading ? (
          <div
            className='flex justify-center p-4'
            data-testid='dataset-loading'
          >
            <div className='animate-spin rounded-full h-8 w-8 border-b-2 border-blue-400'></div>
          </div>
        ) : (
          <AgentRunsView
            runDetails={runs}
            agentName={instanceName}
            selectedRuns={getSelectedRunsForDataset(benchmark.dataset_id)}
            toggleRunSelection={toggleRunSelection}
            clearSelectedRuns={() =>
              clearDatasetSelections(benchmark.dataset_id)
            }
            compareSelected={compareSelected}
          />
        ))}
    </div>
  );
};
