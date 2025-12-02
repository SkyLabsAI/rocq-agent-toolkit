// Runs Section Components



import { useNavigate, useSearchParams } from 'react-router-dom';
import type { RunStats } from '../..';
import { RunsHeader } from './run-header';
import { TaskRow } from './run-row';

interface RunSummaryProps {
  runStats: RunStats[];
  onRemove?: (id: string) => void;
}

export const RunSummary: React.FC<RunSummaryProps> = ({ runStats, onRemove }) => {
  const navigate = useNavigate();
  const [searchParams] = useSearchParams();
  const agent = searchParams.get('agent') || '';
  const runs = runStats.map(r => r.id);

  const defaultHandleRemove = (removeId: string) => {
    const newRuns = runs.filter(id => id !== removeId);
    const url = `/compare?agent=${encodeURIComponent(agent)}&runs=${encodeURIComponent(newRuns.join(','))}`;
    navigate(url);
  };

  const handleRemove = onRemove || defaultHandleRemove;

  return (
    <>
      <RunsHeader title="Runs" keys={["Tasks", "Success %", "LLM Calls", "Total Token", "Avg Exec Time (s)"]} />
      {runStats.map((runStat, index) => (
        <TaskRow key={index} stats={[runStat.id, runStat.tasks, (runStat.successRate*100).toFixed(2),  runStat.totalLlmCalls.toFixed(2), runStat.totalTokens.toFixed(2), runStat.avgExecutionTime.toFixed(2), ]} onClick={() => handleRemove(runStat.id)} />
      ))}
    </>
  );
};