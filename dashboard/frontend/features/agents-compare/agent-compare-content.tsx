import React, { useEffect, useMemo, useState } from 'react';
import { useSearchParams, useNavigate } from 'react-router-dom';
import { useAgents } from '@/hooks/useAgentsSummary';
import { getRunDetails } from '@/services/dataservice';
import { RunDetailsResponse } from '@/types/types';
import { CompareRunsHeader } from '../runs-compare/compare-page-content/compare-page-header';
import { RunSummary } from '../runs-compare/compare-page-content/compare-page-summary';
import { ComparisonTable } from '../runs-compare/compare-page-content/compare-table';
import { computeRunStats, transformRunsToTaskRows } from '../runs-compare/compare-page-content/utils';
import { RunStats, RunTaskCell } from '../runs-compare';
import ComparisonModal from '@/components/base/comparisonModal';

export const AgentCompareContent: React.FC = () => {
  const [sp] = useSearchParams();
  const navigate = useNavigate();
  const { agentData, isLoading: agentDataLoading } = useAgents();


  const selectedAgents = sp.get('agents') || '';
  const agentNames = useMemo(() => {
    return selectedAgents
      .split(',')
      .map(name => name.trim())
      .filter(Boolean);
  }, [selectedAgents]);

  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [bestRuns, setBestRuns] = useState<RunDetailsResponse[]>([]);

  // Remove an agent from the comparison
  const handleRemove = (removeId: string) => {
    const newAgents = agentNames.filter(name => name !== removeId);
    if (newAgents.length === 0) {
      navigate('/');
      return;
    }
    const url = `/compare/agents?agents=${encodeURIComponent(newAgents.join(','))}`;
    navigate(url);
  };

  useEffect(() => {
    const fetchBestRuns = async () => {
      if (agentNames.length === 0) {
        setLoading(false);
        return;
      }

      // Wait for agentData to be loaded before proceeding
      if (agentDataLoading) {
        return;
      }

      setError(null);

      try {
        // Find the best runs for selected agents
        const agentsToCompare = agentData.filter(agent =>
          agentNames.includes(agent.agent_name)
        );

        // Get best run IDs
        const bestRunIds = agentsToCompare
          .map(agent => agent.best_run?.run_id)
          .filter(Boolean) as string[];

        if (bestRunIds.length === 0) {
          console.warn('No valid run IDs found for agents:', agentNames);
          setBestRuns([]);
          setLoading(false);
          return;
        }

        // Fetch run details for the best runs
        const runDetails = await getRunDetails(bestRunIds);
        setBestRuns(runDetails);
      } catch (err) {
        console.error('Error fetching best runs:', err);
        setError(
          err instanceof Error ? err.message : 'Failed to fetch run details'
        );
        setBestRuns([]);
      } finally {
        setLoading(false);
      }
    };

    fetchBestRuns();
  }, [agentNames, agentData, agentDataLoading]);

  const stats = useMemo(
    () => bestRuns.map(run => {
      const runStats = computeRunStats(run);
      // For agent comparison, use agent name as both id and name for display
      return {
        ...runStats,
        id: run.agent_name, // Use agent name for removal
        name: run.agent_name, // Use agent name for display
      };
    }),
    [bestRuns]
  );

  // Create task map with only common tasks across all runs
  const taskMap = useMemo(() => {
    if (bestRuns.length === 0) return {};

    const map: Record<string, RunTaskCell[]> = {};
    const taskCounts: Record<string, number> = {};

    // First pass: count how many runs have each task
    bestRuns.forEach(run => {
      const seenTasks = new Set<string>();
      run.tasks.forEach(task => {
        if (!seenTasks.has(task.task_id)) {
          seenTasks.add(task.task_id);
          taskCounts[task.task_id] = (taskCounts[task.task_id] || 0) + 1;
        }
      });
    });

    // Second pass: only include tasks that appear in ALL runs
    const commonTaskIds = Object.keys(taskCounts).filter(
      taskId => taskCounts[taskId] === bestRuns.length
    );

    // Build the task map with only common tasks
    commonTaskIds.forEach(taskId => {
      map[taskId] = bestRuns.map(run => {
        const task = run.tasks.find(t => t.task_id === taskId);
        return {
          run,
          task: task || undefined,
        };
      });
    });

    return map;
  }, [bestRuns]);

  const [showTasks, setShowTasks] = useState(true);
  const [selectedTaskId, setSelectedTaskId] = useState<string | null>(null);
  const [comparisonModalTaskId, setComparisonModalTaskId] = useState<string | null>(null);
  
  const allTaskIds = useMemo(() => Object.keys(taskMap).sort(), [taskMap]);

  const selectTask = (taskId: string) => {
    setSelectedTaskId(prev => (prev === taskId ? null : taskId));
  };

  const taskRows = useMemo(() => transformRunsToTaskRows(bestRuns), [bestRuns]);

  if (loading) {
    return (
      <div className='flex items-center justify-center h-64'>
        <div className='text-text-disabled'>Loading agent comparison data...</div>
      </div>
    );
  }

  if (error) {
    return (
      <div className='flex items-center justify-center h-64'>
        <div className='text-text-danger'>{error}</div>
      </div>
    );
  }

 

  return (
    <>
      {/* Header */}
      <CompareRunsHeader 
        title='Compare Agents (Best Runs)' 
        secondary={`Comparing best runs of: ${agentNames.join(', ')}`}
      />
      
      {stats.length > 0 && (
        <>
          <RunSummary runStats={stats} onRemove={handleRemove} />
          <ComparisonTable
            runs={bestRuns}
            taskMap={taskMap}
            allTaskIds={allTaskIds}
            selectedTaskId={selectedTaskId}
            showTasks={showTasks}
            onSelectTask={selectTask}
            onOpenModal={setComparisonModalTaskId}
            taskRowData={taskRows}
            onToggleShowTasks={() => setShowTasks(s => !s)}
          />
        </>
      )}

      {/* Show info about common tasks */}
      {allTaskIds.length < (bestRuns[0]?.tasks.length || 0) && (
        <div className='mt-4 p-4 bg-background-information/10 border border-blue-500/30 rounded-lg'>
          <p className='text-text-information text-sm'>
            <strong>Note:</strong> Only showing {allTaskIds.length} tasks that are common across all {bestRuns.length} runs.
            {bestRuns.map(run => `${run.agent_name}: ${run.tasks.length} tasks`).join(', ')}
          </p>
        </div>
      )}

      {/* Comparison Modal */}
      {comparisonModalTaskId && (
        <ComparisonModal
          isOpen={!!comparisonModalTaskId}
          onClose={() => setComparisonModalTaskId(null)}
          taskId={comparisonModalTaskId}
          items={bestRuns.map(run => {
            const cell = taskMap[comparisonModalTaskId]?.[bestRuns.indexOf(run)];
            return {
              label: `${run.agent_name} (${run.run_id})`,
              task: cell?.task || null,
            };
          })}
        />
      )}
    </>
  );
};