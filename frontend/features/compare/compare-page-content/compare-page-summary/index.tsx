// Runs Section Components

import { RunStats } from "../..";
import { RunsHeader } from "./run-header";
import { TaskRow } from "./run-row";

interface RunSummaryProps {
  runStats: RunStats[];
}

export const RunSummary: React.FC<RunSummaryProps> = ({ runStats }) => {
  return (
    <>
        <RunsHeader />
        {runStats.map((runStat, index) => (
          <TaskRow key={index} stat={runStat} />
        ))}
    
    </>
  );
};