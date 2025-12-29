import { useEffect, useState } from 'react';
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

  // Fetch runs on mount to have them available for the compare button
  useEffect(() => {
    if (runs.length === 0) {
      fetchRuns();
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

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

  const handleCompareBestRun = (e: React.MouseEvent) => {
    e.stopPropagation();
    if (runs.length === 0) return;

    // Find the best run (highest success rate)
    const bestRun = runs.reduce((best, current) => {
      const bestRate = best.success_count / best.total_tasks;
      const currentRate = current.success_count / current.total_tasks;
      if (currentRate > bestRate) return current;
      return best;
    }, runs[0]);

    // Toggle selection of the best run
    if (isRunSelected(bestRun.run_id, benchmark.dataset_id)) {
      deselectRun(bestRun.run_id, benchmark.dataset_id);
    } else {
      selectRun(bestRun.run_id, benchmark.dataset_id);
    }
  };

  const getBestRunId = () => {
    if (runs.length === 0) return null;
    const bestRun = runs.reduce((best, current) => {
      const bestRate = best.success_count / best.total_tasks;
      const currentRate = current.success_count / current.total_tasks;
      if (currentRate > bestRate) return current;
      return best;
    }, runs[0]);
    return bestRun.run_id;
  };

  const bestRunId = getBestRunId();
  const isBestRunSelected =
    bestRunId && isRunSelected(bestRunId, benchmark.dataset_id);

  return (
    <div
      className='border-l-2 border-text-disabled/20 ml-6 mb-1'
      data-testid={`instance-dataset-card-${benchmark.dataset_id}`}
    >
      <div
        className='bg-elevation-surface-overlay/50 hover:bg-white/3 overflow-hidden py-2 px-4 flex justify-between items-center cursor-pointer transition-colors'
        onClick={handleToggle}
      >
        <div className='flex gap-2 items-center text-text'>
          <ChevronUpIcon
            className={cn('size-3.5 text-text-disabled', {
              'rotate-180': isOpen,
            })}
          />
          <span
            className='text-[13px] text-text-disabled'
            data-testid='dataset-name'
          >
            📊 {benchmark.dataset_id}
          </span>
        </div>

        <div className='flex items-center gap-2'>
          <span className='text-text-disabled text-xs'>
            {runs.length > 0 ? `${runs.length} runs` : ''}
          </span>
          {runs.length > 0 && (
            <button
              onClick={handleCompareBestRun}
              className={cn(
                'px-2 py-1 text-xs rounded transition-colors',
                isBestRunSelected
                  ? 'bg-primary-default text-white'
                  : 'bg-elevation-surface-raised text-text-disabled hover:bg-elevation-surface-overlay hover:text-text'
              )}
              title={
                isBestRunSelected
                  ? 'Remove best run from comparison'
                  : 'Add best run to comparison'
              }
            >
              {isBestRunSelected ? '✓ Best' : '+ Best'}
            </button>
          )}
        </div>
      </div>
      {isOpen &&
        (isLoading ? (
          <div
            className='flex justify-center p-3'
            data-testid='dataset-loading'
          >
            <div className='animate-spin rounded-full h-5 w-5 border-b-2 border-blue-400'></div>
          </div>
        ) : (
          <div className='pl-2'>
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
          </div>
        ))}
    </div>
  );
};
