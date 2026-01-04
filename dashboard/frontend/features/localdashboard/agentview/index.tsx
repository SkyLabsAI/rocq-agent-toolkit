import { usePathname, useRouter } from 'next/navigation';
import React, { useEffect, useState } from 'react';

import StickyCompareBar from '@/components/sticky-compare-bar';
import { GlobalCompareProvider } from '@/contexts/global-compare-context';
import TaskDetailsModal from '@/features/task-details-modal';
import { useAgents } from '@/hooks/use-agent-summaries';
import AgentListIcon from '@/icons/agent-list';
import { SortIcon } from '@/icons/sort/sort';
import { type AgentSummaryTemp } from '@/services/dataservice';

import AgentDetails from './agent-details';

const AgentView: React.FC = () => {
  const { agentData, modalState, closeModal } = useAgents();
  const [selectedAgents, setSelectedAgent] = useState<AgentSummaryTemp[]>([]);
  const [selectedRuns, setSelectedRuns] = useState<string[]>([]);

  type SortableKey =
    | 'cls_name'
    | 'success_rate'
    | 'avg_cpu_time_sec'
    | 'avg_total_tokens'
    | 'avg_llm_invocation_count';

  const [sortConfig, setSortConfig] = useState<{
    key: SortableKey;
    direction: 'asc' | 'desc';
  } | null>(null);
  const router = useRouter();
  const pathname = usePathname();

  const compareSelected = () => {
    if (selectedAgents.length < 1) return;
    const query = new URLSearchParams({
      agents: selectedAgents.map(a => a.agentName).join(','),
    }).toString();
    router.push(`/compare/agents?${query}`);
  };

  const compareSelectedRuns = () => {
    if (selectedRuns.length < 1) return;
    const query = new URLSearchParams({
      runs: selectedRuns.join(','),
    }).toString();
    router.push(`/compare?${query}`);
  };

  const clearSelectedRuns = () => {
    setSelectedRuns([]);
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
      a.cls_name.localeCompare(b.cls_name)
    );

    if (!sortConfig) return sorted;

    return sorted.sort((a, b) => {
      let aValue: number | string = 0;
      let bValue: number | string = 0;

      if (sortConfig.key === 'cls_name') {
        aValue = a.cls_name;
        bValue = b.cls_name;
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

  // Clear selected runs when navigating to different pages
  useEffect(() => {
    const isComparePage = pathname?.startsWith('/compare');
    if (isComparePage) {
      clearSelectedRuns();
      setSelectedAgent([]);
    }
  }, [pathname]);

  return (
    <GlobalCompareProvider>
      <div data-testid='agent-view'>
        <table
          className='w-full text-left border-collapse'
          data-testid='agents-table'
        >
          <tbody className='divide-y divide-elevation-surface-overlay'>
            <tr className='text-text' data-testid='agents-header-row'>
              <td>
                <button
                  data-testid='sort-by-agent-name'
                  onClick={() => handleSort('cls_name')}
                  className='flex gap-1 items-center px-6 text-[16px] py-5 hover:text-primary-default transition-colors cursor-pointer w-full'
                >
                  <AgentListIcon className='text-icon-success size-4' />
                  Agents
                  <SortIcon
                    className={`ml-2 transition-transform size-4 ${
                      sortConfig?.key === 'cls_name'
                        ? sortConfig.direction === 'desc'
                          ? 'text-primary-default'
                          : 'rotate-180 text-primary-default'
                        : 'text-text-disabled'
                    }`}
                  />
                </button>
              </td>
            </tr>
            {getSortedAgents().map(agent => (
              <AgentDetails key={agent.cls_checksum} agent={agent} />
            ))}
          </tbody>
        </table>
      </div>

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

      <StickyCompareBar
        selectedItems={selectedAgents.map(s => s.agentName)}
        onCompareSelected={compareSelected}
        onClearSelection={() => {
          setSelectedAgent([]);
        }}
        attribute='Agents'
      />

      {selectedRuns.length > 0 && (
        <StickyCompareBar
          selectedItems={selectedRuns}
          onCompareSelected={compareSelectedRuns}
          onClearSelection={clearSelectedRuns}
          attribute='Runs'
        />
      )}
    </GlobalCompareProvider>
  );
};

export default AgentView;
