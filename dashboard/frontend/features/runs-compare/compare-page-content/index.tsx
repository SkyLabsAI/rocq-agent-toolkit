import { useSearchParams } from 'next/navigation';
import { useEffect, useMemo, useState } from 'react';

import ComparisonModal from '@/components/base/comparisonModal';
import { getRunDetails } from '@/services/dataservice';
import { type RunDetailsResponse } from '@/types/types';

import { type RunTaskCell } from '..';
import { CompareRunsHeader } from './compare-page-header';
import { RunSummary } from './compare-page-summary';
import { ComparisonTable } from './compare-table';
import { computeRunStats, transformRunsToTaskRows } from './utils';

export const ComparePageContent: React.FC = () => {
  const sp = useSearchParams();
  const runsParam = sp?.get('runs') || '';

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

  const taskRows = useMemo(
    () => transformRunsToTaskRows(selectedRuns),
    [selectedRuns]
  );

  return (
    <>
      {/* Header */}
      <CompareRunsHeader title='Compare Runs' secondary={``} />
      {!loading && !error && stats.length > 0 && (
        <>
          <RunSummary runStats={stats} />
          <ComparisonTable
            runs={selectedRuns}
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
