// Runs Section Components



import { useNavigate, useSearchParams } from 'react-router-dom';
import type { RunStats } from '@/features/compare';
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
      <RunsHeader />
      {runStats.map((runStat, index) => (
        <TaskRow key={index} stat={runStat} onClick={() => handleRemove(runStat.id)} />
      ))}
    </>
  );
};