import { AgentRun } from "@/types/types";

export function isLatestRun(run: AgentRun, runs: AgentRun[]): boolean {
  if (!runs.length) return false;
  const latestTimestamp = runs
    .map(r => r.timestamp_utc)
    .sort((a, b) => b.localeCompare(a))[0];
  return run.timestamp_utc === latestTimestamp;
}