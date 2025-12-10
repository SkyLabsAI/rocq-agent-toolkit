import { useEffect, useState } from 'react';
import { useLocation, useNavigate } from 'react-router-dom';

import RunDetailsView from '@/components/run-details-view';
import { useGlobalCompare } from '@/contexts/global-compare-context';
import { useSelectedRun } from '@/contexts/selected-run-context';
import TaskDetailsModal from '@/features/taskDetailsModal';
import { useAgents } from '@/hooks/use-agent-summaries';
import AgentListIcon from '@/icons/agent-list';
import { ChevronUpIcon } from '@/icons/chevron-up';
import { type Benchmark, type Run } from '@/types/types';
import { cn } from '@/utils/cn';

import { useBenchmarkAgents } from '../../../../hooks/use-dataview';
import AgentDetails from './agent-details';

interface DataItemProps {
  benchmark: Benchmark;
}

export const DataItem: React.FC<DataItemProps> = ({ benchmark }) => {
  const [isOpen, setIsOpen] = useState(false);

  const { agents: agentData } = useBenchmarkAgents(benchmark.dataset_id);

  const { modalState, closeModal, openCodeModal } = useAgents();

  const { selectedRun, setSelectedRun } = useSelectedRun();

  // Use global compare context instead of local state
  const {
    selectAgent,
    deselectAgent,
    selectRun,
    deselectRun,
    getSelectedRunsForDataset,
    isAgentSelected,
    isRunSelected,
    clearDatasetSelections,
  } = useGlobalCompare();

  type SortableKey =
    | 'agent_name'
    | 'success_rate'
    | 'avg_cpu_time_sec'
    | 'avg_total_tokens'
    | 'avg_llm_invocation_count';

  const [sortConfig, setSortConfig] = useState<{
    key: SortableKey;
    direction: 'asc' | 'desc';
  } | null>(null);
  const navigate = useNavigate();
  const location = useLocation();

  const toggleRunSelection = (run: Run) => {
    if (isRunSelected(run.run_id, benchmark.dataset_id)) {
      deselectRun(run.run_id, benchmark.dataset_id);
    } else {
      selectRun(run.run_id, benchmark.dataset_id);
    }
  };

  // Sorting function
  const handleSort = (key: SortableKey) => {
    let direction: 'asc' | 'desc' = 'asc';
    if (
      sortConfig &&
      sortConfig.key === key &&
      sortConfig.direction === 'asc'
    ) {
      direction = 'desc';
    }
    setSortConfig({ key, direction });
  };

  // Sort the agents based on sortConfig
  const getSortedAgents = () => {
    const sorted = [...agentData].sort((a, b) =>
      a.agent_name.localeCompare(b.agent_name)
    );

    if (!sortConfig) return sorted;

    return sorted.sort((a, b) => {
      let aValue: number | string = 0;
      let bValue: number | string = 0;

      if (sortConfig.key === 'agent_name') {
        aValue = a.agent_name;
        bValue = b.agent_name;
      } else {
        // Get values from best_run
        aValue = a.best_run?.[sortConfig.key] ?? 0;
        bValue = b.best_run?.[sortConfig.key] ?? 0;
      }

      if (typeof aValue === 'string' && typeof bValue === 'string') {
        return sortConfig.direction === 'asc'
          ? aValue.localeCompare(bValue)
          : bValue.localeCompare(aValue);
      }

      const aNum = Number(aValue);
      const bNum = Number(bValue);
      return sortConfig.direction === 'asc' ? aNum - bNum : bNum - aNum;
    });
  };

  // Clear dataset selections when navigating to run details view
  useEffect(() => {
    if (selectedRun) {
      clearDatasetSelections(benchmark.dataset_id);
    }
  }, [selectedRun, benchmark.dataset_id, clearDatasetSelections]);

  // Clear dataset selections when navigating to different pages
  useEffect(() => {
    const isComparePage = location.pathname.startsWith('/compare');
    if (isComparePage) {
      clearDatasetSelections(benchmark.dataset_id);
    }
  }, [location.pathname, benchmark.dataset_id, clearDatasetSelections]);

  return (
    <div>
      <div
        className='bg-elevation-surface-raised overflow-hidden px-4.5 py-5 flex justify-between items-center'
        onClick={() => setIsOpen(!isOpen)}
      >
        <div className='flex gap-1 items-center text-text'>
          <ChevronUpIcon className={cn('size-6', { 'rotate-180': isOpen })} />
          <span className='text-[16px] cursor-pointer '>
            {benchmark.dataset_id}
          </span>
        </div>

        <span className='text-text-disabled text-sm '>{''}</span>
      </div>
      {isOpen && (
        <>
          {!selectedRun && (
            <div className=''>
              <table className='w-full text-left border-collapse'>
                <tbody className='divide-y divide-elevation-surface-overlay'>
                  <tr className='text-text'>
                    <td>
                      <button
                        onClick={() => handleSort('agent_name')}
                        className='flex gap-1 items-center px-6 text-[16px] py-5 hover:text-primary-default transition-colors cursor-pointer w-full'
                      >
                        <AgentListIcon className='text-icon-success size-4' />
                        Agents
                        <ChevronUpIcon
                          className={`ml-2 transition-transform ${
                            sortConfig?.key === 'agent_name'
                              ? sortConfig.direction === 'desc'
                                ? 'text-primary-default'
                                : 'rotate-180 text-primary-default'
                              : 'text-text-disabled'
                          }`}
                        />
                      </button>
                    </td>
                    <td>
                      <button
                        onClick={() => handleSort('success_rate')}
                        className='px-6 py-4 font-[16px] text-text-disabled hover:text-primary-default transition-colors cursor-pointer flex items-center gap-1'
                      >
                        Success Rate
                        <ChevronUpIcon
                          className={`transition-transform ${
                            sortConfig?.key === 'success_rate'
                              ? sortConfig.direction === 'desc'
                                ? 'text-primary-default'
                                : 'rotate-180 text-primary-default'
                              : 'text-text-disabled'
                          }`}
                        />
                      </button>
                    </td>
                    <td>
                      <button
                        onClick={() => handleSort('avg_cpu_time_sec')}
                        className='px-6 py-4 font-[16px] text-text-disabled hover:text-primary-default transition-colors cursor-pointer flex items-center gap-1'
                      >
                        Avg Time (s)
                        <ChevronUpIcon
                          className={`transition-transform ${
                            sortConfig?.key === 'avg_cpu_time_sec'
                              ? sortConfig.direction === 'desc'
                                ? 'text-primary-default'
                                : 'rotate-180 text-primary-default'
                              : 'text-text-disabled'
                          }`}
                        />
                      </button>
                    </td>
                    <td>
                      <button
                        onClick={() => handleSort('avg_total_tokens')}
                        className='px-6 py-4 font-[16px] text-text-disabled hover:text-primary-default transition-colors cursor-pointer flex items-center gap-1'
                      >
                        Avg Tokens
                        <ChevronUpIcon
                          className={`transition-transform ${
                            sortConfig?.key === 'avg_total_tokens'
                              ? sortConfig.direction === 'desc'
                                ? 'text-primary-default'
                                : 'rotate-180 text-primary-default'
                              : 'text-text-disabled'
                          }`}
                        />
                      </button>
                    </td>
                    <td>
                      <button
                        onClick={() => handleSort('avg_llm_invocation_count')}
                        className='px-6 py-4 font-[16px] text-text-disabled hover:text-primary-default transition-colors cursor-pointer flex items-center gap-1'
                      >
                        Avg LLM Calls
                        <ChevronUpIcon
                          className={`transition-transform ${
                            sortConfig?.key === 'avg_llm_invocation_count'
                              ? sortConfig.direction === 'desc'
                                ? 'text-primary-default'
                                : 'rotate-180 text-primary-default'
                              : 'text-text-disabled'
                          }`}
                        />
                      </button>
                    </td>
                    <td className='px-6 py-4 font-[16px] text-center text-text-disabled'>
                      Actions
                    </td>
                  </tr>
                  {getSortedAgents().map(agent => (
                    <AgentDetails
                      key={agent.agent_name}
                      agent={agent}
                      datasetId={benchmark.dataset_id}
                      isSelected={isAgentSelected(
                        agent.agent_name,
                        benchmark.dataset_id
                      )}
                      toggleSelection={() => {
                        if (
                          isAgentSelected(
                            agent.agent_name,
                            benchmark.dataset_id
                          )
                        ) {
                          deselectAgent(agent.agent_name, benchmark.dataset_id);
                        } else {
                          selectAgent(agent.agent_name, benchmark.dataset_id);
                        }
                      }}
                      selectedRuns={getSelectedRunsForDataset(
                        benchmark.dataset_id
                      )}
                      toggleRunSelection={toggleRunSelection}
                      clearSelectedRuns={() =>
                        clearDatasetSelections(benchmark.dataset_id)
                      }
                      compareSelectedRuns={() => {
                        const selectedRunIds = getSelectedRunsForDataset(
                          benchmark.dataset_id
                        );
                        if (selectedRunIds.length < 1) return;
                        const query = new URLSearchParams({
                          runs: selectedRunIds.join(','),
                        }).toString();
                        navigate({
                          pathname: '/compare',
                          search: `?${query}`,
                        });
                      }}
                    />
                  ))}
                </tbody>
              </table>
            </div>
          )}

          {selectedRun && (
            <RunDetailsView
              run={selectedRun}
              onBack={() => setSelectedRun(null)}
              openCodeModal={openCodeModal}
            />
          )}

          <TaskDetailsModal
            isOpen={modalState.isOpen}
            onClose={closeModal}
            details={modalState.logs}
            title={
              modalState.selectedTask
                ? `Observability Logs - ${modalState.selectedTask.task_id}`
                : 'Task Logs'
            }
            taskId={modalState.selectedTask?.task_id}
          />
        </>
      )}
    </div>
  );
};
