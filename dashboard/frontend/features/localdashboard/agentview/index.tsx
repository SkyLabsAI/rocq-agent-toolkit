import React, { useEffect, useState } from 'react';
import { ChevronUpIcon } from '@/icons/chevron-up';
import AgentListIcon from '@/icons/agent-list';
import AgentDetails from './agent-details';
import { AgentSummaryTemp } from '@/services/dataservice';
import TaskDetailsModal from '@/features/taskDetailsModal';
import RunDetailsView from '@/components/RunDetailsView';
import StickyCompareBar from '@/components/StickyCompareBar';
import { useSelectedRun } from '@/contexts/SelectedRunContext';
import { useLocation, useNavigate } from 'react-router-dom';
import { useAgents } from '@/hooks/useAgentsSummary';
import { Run } from '@/types/types';
import { GlobalCompareProvider } from '@/contexts/GlobalCompareContext';

const AgentView: React.FC = ({}) => {
  const { agentData, agentDetailData, modalState, closeModal, openCodeModal } =
    useAgents();

  const { selectedRun, setSelectedRun } = useSelectedRun();
  const [activeAgent, setActiveAgent] = React.useState<string | null>(null);
  const [selectedAgents, setSelectedAgent] = useState<AgentSummaryTemp[]>([]);
  const [selectedRuns, setSelectedRuns] = useState<string[]>([]);

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

  const compareSelected = () => {
    if (selectedAgents.length < 1) return;
    const query = new URLSearchParams({
      agents: selectedAgents.map(a => a.agentName).join(','),
    }).toString();
    navigate({
      pathname: '/compare/agents',
      search: `?${query}`,
    });
  };

  const compareSelectedRuns = () => {
    if (selectedRuns.length < 1) return;
    const query = new URLSearchParams({
      runs: selectedRuns.join(','),
    }).toString();
    navigate({
      pathname: '/compare',
      search: `?${query}`,
    });
  };

  const toggleRunSelection = (run: Run) => {
    setSelectedRuns(prev =>
      prev.includes(run.run_id)
        ? prev.filter(id => id !== run.run_id)
        : [...prev, run.run_id]
    );
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

  // Clear selected runs when navigating to run details view
  useEffect(() => {
    if (selectedRun) {
      clearSelectedRuns();
      setSelectedAgent([]);
    }
  }, [selectedRun]);

  // Clear selected runs when navigating to different pages
  useEffect(() => {
    const isComparePage = location.pathname.startsWith('/compare');
    if (isComparePage) {
      clearSelectedRuns();
      setSelectedAgent([]);
    }
  }, [location.pathname]);

  return (
    <GlobalCompareProvider>
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
                {/* <td className='px-6 py-4 font-[16px] text-center text-text-disabled'>
                  Actions
                </td> */}
              </tr>
              {getSortedAgents().map((agent, index) => (
                <AgentDetails
                  key={agent.agent_name}
                  agent={agent}
                  agentDetailData={agentDetailData[index]}
                  activeAgent={activeAgent === agent.agent_name}
                  setActiveAgent={setActiveAgent}
                  isSelected={selectedAgents.some(
                    a => a.agentName === agent.agent_name
                  )}
                  toggleSelection={() => {
                    setSelectedAgent(prevSelectedAgents => {
                      if (
                        prevSelectedAgents.some(
                          a => a.agentName === agent.agent_name
                        )
                      ) {
                        // Remove the agent if already selected
                        return prevSelectedAgents.filter(
                          a => a.agentName !== agent.agent_name
                        );
                      } else {
                        // Add the new agent while keeping the previous selections
                        return [
                          ...prevSelectedAgents,
                          {
                            agentName: agent.agent_name,
                          } as AgentSummaryTemp,
                        ];
                      }
                    });
                  }}
                  selectedRuns={selectedRuns}
                  toggleRunSelection={toggleRunSelection}
                  clearSelectedRuns={clearSelectedRuns}
                  compareSelectedRuns={compareSelectedRuns}
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

      <StickyCompareBar
        selectedItems={selectedAgents.map(s => s.agentName)}
        onCompareSelected={compareSelected}
        onClearSelection={() => {
          setSelectedAgent([]);
        }}
        attribute='Agents'
      />

      {selectedRuns.length > 0 && !selectedRun && (
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
