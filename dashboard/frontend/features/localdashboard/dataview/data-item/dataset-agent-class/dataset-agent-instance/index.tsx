import { useRouter } from 'next/navigation';
import { useState } from 'react';

import { useGlobalCompare } from '@/contexts/global-compare-context';
import AgentRunsView from '@/features/localdashboard/agent-runs-view';
import { ChevronUpIcon } from '@/icons/chevron-up';
import { type AgentInstanceSummary, type Run } from '@/types/types';
import { cn } from '@/utils/cn';

import { useDatasetAgentInstance } from './use-dataset-agent-instance';

interface DatasetAgentInstanceProps {
  instance: AgentInstanceSummary;
  datasetId: string;
}

export const DatasetAgentInstance: React.FC<DatasetAgentInstanceProps> = ({
  instance,
  datasetId,
}) => {
  const [isOpen, setIsOpen] = useState(false);
  const { runs, isLoading, fetchRuns } = useDatasetAgentInstance(
    datasetId,
    instance.agent_checksum
  );
  const router = useRouter();

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
    if (isRunSelected(run.run_id, datasetId)) {
      deselectRun(run.run_id, datasetId);
    } else {
      selectRun(run.run_id, datasetId);
    }
  };

  const compareSelected = () => {
    const selectedRunIds = getSelectedRunsForDataset(datasetId);
    if (selectedRunIds.length < 1) return;
    const query = new URLSearchParams({
      runs: selectedRunIds.join(','),
    }).toString();
    router.push(`/compare?${query}`);
  };

  return (
    <div
      className='border-l-2 border-background-warning/30 ml-8 mb-2 rounded-r-md overflow-hidden'
      data-testid={`dataset-instance-card-${instance.agent_checksum}`}
    >
      <div
        className='bg-elevation-surface-raised/60 hover:bg-elevation-surface-raised/80 overflow-hidden py-2.5 px-4 flex justify-between items-center cursor-pointer transition-colors gap-4'
        onClick={handleToggle}
      >
        <div className='flex gap-3 items-center text-text min-w-0 shrink'>
          <ChevronUpIcon
            className={cn('size-3.5 text-text-disabled shrink-0', {
              'rotate-180': isOpen,
            })}
          />
          <div className='flex items-center gap-2 min-w-0'>
            <div className='h-4 w-4 bg-background-warning rounded flex items-center justify-center shrink-0'>
              <span className='text-text-warning font-semibold text-[10px]'>
                {instance.name.charAt(0).toUpperCase()}
              </span>
            </div>
            <div className='flex flex-col min-w-0'>
              <span
                className='text-sm font-medium truncate text-text'
                data-testid='instance-name'
              >
                {instance.name}
              </span>
            </div>
          </div>
        </div>

        <div className='flex items-center gap-2 shrink-0'>
          <div className='flex gap-2.5 text-xs bg-elevation-surface-overlay px-2.5 py-1 rounded-md'>
            <div className='flex flex-col items-end'>
              <span className='text-text-disabled'>Success</span>
              <span className='text-text font-medium'>
                {((instance.best_run?.success_rate ?? 0) * 100).toFixed(1)}%
              </span>
            </div>
            <div className='flex flex-col items-end'>
              <span className='text-text-disabled'>Time</span>
              <span className='text-text font-medium'>
                {(instance.best_run?.avg_cpu_time_sec ?? 0).toFixed(2)}s
              </span>
            </div>
            <div className='flex flex-col items-end'>
              <span className='text-text-disabled'>Tokens</span>
              <span className='text-text font-medium'>
                {(instance.best_run?.avg_total_tokens ?? 0).toFixed(0)}
              </span>
            </div>
            <div className='flex flex-col items-end'>
              <span className='text-text-disabled'>Runs</span>
              <span className='text-text font-medium'>
                {instance.total_runs}
              </span>
            </div>
          </div>
        </div>
      </div>

      {isOpen && (
        <div className='pl-4' data-testid='instance-expanded-content'>
          {isLoading ? (
            <div
              className='flex justify-center p-4'
              data-testid='instance-loading'
            >
              <div className='animate-spin rounded-full h-6 w-6 border-b-2 border-blue-400'></div>
            </div>
          ) : runs.length === 0 ? (
            <div
              className='text-center py-6 text-text-disabled text-sm'
              data-testid='instance-no-runs'
            >
              No runs available for this instance.
            </div>
          ) : (
            <AgentRunsView
              runDetails={runs}
              agentName={instance.name}
              selectedRuns={getSelectedRunsForDataset(datasetId)}
              toggleRunSelection={toggleRunSelection}
              clearSelectedRuns={() => clearDatasetSelections(datasetId)}
              compareSelected={compareSelected}
            />
          )}
        </div>
      )}
    </div>
  );
};
