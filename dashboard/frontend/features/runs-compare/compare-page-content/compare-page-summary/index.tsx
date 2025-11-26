// Runs Section Components



import { useNavigate, useSearchParams } from 'react-router-dom';
import type { RunStats } from '../..';
import { RunsHeader } from './run-header';
import { TaskRow } from './run-row';

interface RunSummaryProps {
  runStats: RunStats[];
}

export const RunSummary: React.FC<RunSummaryProps> = ({ runStats }) => {
  const navigate = useNavigate();
  const [searchParams] = useSearchParams();
  const agent = searchParams.get('agent') || '';
  const runs = runStats.map(r => r.id);

  const handleRemove = (removeId: string) => {
    const newRuns = runs.filter(id => id !== removeId);
    const url = `/compare?agent=${encodeURIComponent(agent)}&runs=${encodeURIComponent(newRuns.join(','))}`;
    navigate(url);
  };

  return (
    <>
      <RunsHeader title="Runs" keys={["Tasks", "Success %", "LLM Calls", "Total Token", "Avg Exec Time (s)"]} />
      {runStats.map((runStat, index) => (
        <TaskRow key={index} stats={[runStat.id, runStat.tasks, (runStat.successRate*100).toFixed(2),  runStat.totalLlmCalls, runStat.totalTokens, runStat.avgExecutionTime, ]} onClick={() => handleRemove(runStat.id)} />
      ))}
    </>
  );
};