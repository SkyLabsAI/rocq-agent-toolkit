import { useEffect, useState } from 'react';
import { getObservabilityLogs } from '@/services/dataservice';
import type { TaskOutput } from '@/types/types';

export interface ComparisonItem {
  label: string;
  task: TaskOutput | null;
}

export interface TaskLogs {
  [itemIndex: number]: Record<string, unknown> | null;
}

export function useComparisonLogs(isOpen: boolean, items: ComparisonItem[]) {
  const [taskLogs, setTaskLogs] = useState<TaskLogs>({});
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    if (!isOpen || items.length === 0) return;

    const fetchLogs = async () => {
      setLoading(true);
      setError(null);
      const logs: TaskLogs = {};
      try {
        await Promise.all(
          items.map(async (item, index) => {
            if (item.task) {
              try {
                const taskLogs = await getObservabilityLogs(item.task.run_id, item.task.task_id);
                logs[index] = taskLogs;
              } catch (err) {
                logs[index] = null;
              }
            } else {
              logs[index] = null;
            }
          })
        );
        setTaskLogs(logs);
      } catch (err) {
        setError('Failed to load comparison data');
      } finally {
        setLoading(false);
      }
    };
    fetchLogs();
  }, [isOpen, items]);

  return { taskLogs, loading, error };
}
