import ComparisonModal from '@/components/base/comparisonModal';
import Layout from '@/layouts/common';
import { getRunDetails } from '@/services/dataservice';
import { RunDetailsResponse } from '@/types/types';
import { useSearchParams } from 'next/navigation';
import { useEffect, useMemo, useState } from 'react';
import { RunStats, RunTaskCell } from '..';
import { CompareRunsHeader } from './compare-page-header';
import { RunSummary } from './compare-page-summary';
import { ComparisonHeaderBar } from './compare-header-bar';
import { ComparisonTable } from './compare-table';

const computeRunStats = (run: RunDetailsResponse): RunStats => {
  const tasks = run.tasks.length;
  const successes = run.tasks.filter(t => t.status === 'Success').length;
  return {
    id: run.run_id,
    name: run.agent_name,
    tasks,
    successRate: tasks === 0 ? 0 : successes / tasks,
    totalLlmCalls: run.tasks.reduce(
      (a, t) => a + (t.metrics?.llm_invocation_count || 0),
      0
    ),
    totalTokens: run.tasks.reduce(
      (a, t) => a + (t.metrics?.token_counts?.total_tokens || 0),
      0
    ),
    avgExecutionTime:
      tasks === 0
        ? 0
        : run.tasks.reduce(
            (a, t) => a + (t.metrics?.resource_usage?.execution_time_sec || 0),
            0
          ) / tasks,
  };
};

const normalizeFailureReason = (fr: unknown): string => {
  if (fr == null) return '';
  if (Array.isArray(fr)) {
    return fr
      .map(x => (typeof x === 'string' ? x : JSON.stringify(x)))
      .join(' | ');
  }
  if (typeof fr === 'object') {
    const obj = fr as { kind?: string; value?: unknown };
    if (obj.kind) {
      return (
        obj.kind +
        (obj.value
          ? ': ' +
            (typeof obj.value === 'object'
              ? JSON.stringify(obj.value)
              : String(obj.value))
          : '')
      );
    }
    return JSON.stringify(fr);
  }
  return String(fr);
};

export const ComparePageContent: React.FC = () => {
  const sp = useSearchParams();
  const agentName = sp.get('agent') || '';
  const runsParam = sp.get('runs') || '';

  const runIds = useMemo(() => {
    return runsParam
      .split(',')
      .map(r => r.trim())
      .filter(Boolean);
  }, [runsParam]);

  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [selectedRuns, setSelectedRuns] = useState<RunDetailsResponse[]>([]);

  useEffect(() => {
    const fetchRunDetails = async () => {
      if (runIds.length === 0) {
        setLoading(false);
        return;
      }

      setLoading(true);
      setError(null);

      try {
        const runDetails = await getRunDetails(runIds);
        setSelectedRuns(runDetails);
      } catch (err) {
        console.error('Error fetching run details:', err);
        setError(
          err instanceof Error ? err.message : 'Failed to fetch run details'
        );
        setSelectedRuns([]);
      } finally {
        setLoading(false);
      }
    };

    fetchRunDetails();
  }, [runIds]);

  const stats = useMemo(
    () => selectedRuns.map(computeRunStats),
    [selectedRuns]
  );

  const taskMap = useMemo(() => {
    const map: Record<string, RunTaskCell[]> = {};
    selectedRuns.forEach((run, runIdx) => {
      run.tasks.forEach(task => {
        if (!map[task.task_id]) {
          map[task.task_id] = selectedRuns.map(r => ({
            run: r,
            task: undefined,
          }));
        }
        map[task.task_id][runIdx] = { run, task };
      });
    });
    return map;
  }, [selectedRuns]);

  const [showTasks, setShowTasks] = useState(true);
  const [selectedTaskId, setSelectedTaskId] = useState<string | null>(null);
  const [comparisonModalTaskId, setComparisonModalTaskId] = useState<
    string | null
  >(null);
  const allTaskIds = useMemo(() => Object.keys(taskMap).sort(), [taskMap]);

  const selectTask = (taskId: string) => {
    setSelectedTaskId(prev => (prev === taskId ? null : taskId));
  };

  return (
    <>
      {/* Header */}
      <CompareRunsHeader />
      {!loading && !error && stats.length > 0 && (
        <>
          <RunSummary runStats={stats} />
          {/* <ComparisonHeaderBar /> */}
          <ComparisonTable
            runs={selectedRuns}
            taskMap={taskMap}
            allTaskIds={allTaskIds}
            selectedTaskId={selectedTaskId}
            showTasks={showTasks}
            onSelectTask={selectTask}
            onOpenModal={setComparisonModalTaskId}
            onToggleShowTasks={() => setShowTasks(s => !s)}
          />
        </>
      )}

      {/* Comparison Modal */}
      {comparisonModalTaskId && (
        <ComparisonModal
          isOpen={!!comparisonModalTaskId}
          onClose={() => setComparisonModalTaskId(null)}
          taskId={comparisonModalTaskId}
          items={selectedRuns.map(run => {
            const cell =
              taskMap[comparisonModalTaskId]?.[selectedRuns.indexOf(run)];
            return {
              label: run.agent_name,
              task: cell?.task || null,
            };
          })}
        />
      )}
    </>
  );
};
