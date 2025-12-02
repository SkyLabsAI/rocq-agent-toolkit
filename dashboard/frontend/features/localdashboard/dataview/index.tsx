import React, { useEffect, useState } from 'react';
import { ChevronUpIcon } from '@/icons/chevron-up';
import AgentListIcon from '@/icons/agent-list';
import AgentDetails from '../AgentDetails';
import { AgentSummaryTemp } from '@/services/dataservice';
import TaskDetailsModal from '@/features/taskDetailsModal';
import RunDetailsView from '@/components/RunDetailsView';
import StickyCompareBar from '@/components/StickyCompareBar';
import { Run, useSelectedRun } from '@/contexts/SelectedRunContext';
import { useLocation, useNavigate } from 'react-router-dom';
import { useLocalDashboard } from '@/hooks/useLocalDashboard';
import { useBenchmarkAgents, useBenchmarks } from './use-dataview';
import { DataItem } from './data-item';

const DataView: React.FC = ({}) => {
  const { benchmarks} =
    useBenchmarks();

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

  // // Sort the agents based on sortConfig
  // const getSortedAgents = () => {
  //   const sorted = [...agentData].sort((a, b) =>
  //     a.agent_name.localeCompare(b.agent_name)
  //   );

  //   if (!sortConfig) return sorted;

  //   return sorted.sort((a, b) => {
  //     let aValue: number | string = 0;
  //     let bValue: number | string = 0;

  //     if (sortConfig.key === 'agent_name') {
  //       aValue = a.agent_name;
  //       bValue = b.agent_name;
  //     } else {
  //       // Get values from best_run
  //       aValue = a.best_run?.[sortConfig.key] ?? 0;
  //       bValue = b.best_run?.[sortConfig.key] ?? 0;
  //     }

  //     if (typeof aValue === 'string' && typeof bValue === 'string') {
  //       return sortConfig.direction === 'asc'
  //         ? aValue.localeCompare(bValue)
  //         : bValue.localeCompare(aValue);
  //     }

  //     const aNum = Number(aValue);
  //     const bNum = Number(bValue);
  //     return sortConfig.direction === 'asc' ? aNum - bNum : bNum - aNum;
  //   });
  // };

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
   
     <div className='flex flex-col gap-4'>
      {benchmarks.map((benchmark) => (
        <DataItem key={benchmark.dataset_id} benchmark={benchmark} />
      ))}
    
     </div>
  );
};

export default DataView;
