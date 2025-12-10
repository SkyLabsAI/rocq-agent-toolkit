import AgentRunsView from '@/features/localdashboard/AgentRunsView';
import { ChevronUpIcon } from '@/icons/chevron-up';
import { Benchmark, Run } from '@/types/types';
import { cn } from '@/utils/cn';
import { useState } from 'react';
import { useAgentBenchmarks } from './use-benchmark-runs';
import { useGlobalCompare } from '@/contexts/GlobalCompareContext';
import { useNavigate } from 'react-router-dom';

interface AgentBenchMarkProps {
  benchmark: Benchmark;
  agentName: string;
}

export const AgentBenchmark: React.FC<AgentBenchMarkProps> = ({
  benchmark,
  agentName,
}) => {
  const [isOpen, setIsOpen] = useState(false);
  const { runs, isLoading, error, fetchRuns } = useAgentBenchmarks(
    agentName,
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
    <div>
      <div
        className='bg-elevation-surface-raised overflow-hidden py-5 flex justify-between items-center cursor-pointer'
        onClick={handleToggle}
      >
        <div className='flex gap-1 items-center text-text'>
          <ChevronUpIcon className={cn('size-6', { 'rotate-180': isOpen })} />
          <span className='text-[16px] '>{benchmark.dataset_id}</span>
        </div>

        <span className='text-text-disabled text-sm '>{''}</span>
      </div>
      {isOpen &&
        (isLoading ? (
          <div className='flex justify-center p-4'>
            <div className='animate-spin rounded-full h-8 w-8 border-b-2 border-blue-400'></div>
          </div>
        ) : (
          <AgentRunsView
            runDetails={runs}
            agentName={agentName}
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
