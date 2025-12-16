import { type AgentRun } from '@/types/types';

import { isLatestRun } from './agent-runs-view';

describe('isLatestRun', () => {
  const createRun = (runId: string, timestamp: string): AgentRun => ({
    run_id: runId,
    agent_name: 'test-agent',
    timestamp_utc: timestamp,
    total_tasks: 10,
    success_count: 8,
    failure_count: 2,
    dataset_id: 'dataset-1',
    metadata: { tags: {} },
  });

  it('should return false for empty runs array', () => {
    const run = createRun('run-1', '2024-01-01T00:00:00Z');
    expect(isLatestRun(run, [])).toBe(false);
  });

  it('should return true for the latest run', () => {
    const runs = [
      createRun('run-1', '2024-01-01T00:00:00Z'),
      createRun('run-2', '2024-01-02T00:00:00Z'),
      createRun('run-3', '2024-01-03T00:00:00Z'),
    ];

    expect(isLatestRun(runs[2], runs)).toBe(true);
  });

  it('should return false for non-latest runs', () => {
    const runs = [
      createRun('run-1', '2024-01-01T00:00:00Z'),
      createRun('run-2', '2024-01-02T00:00:00Z'),
      createRun('run-3', '2024-01-03T00:00:00Z'),
    ];

    expect(isLatestRun(runs[0], runs)).toBe(false);
    expect(isLatestRun(runs[1], runs)).toBe(false);
  });

  it('should handle single run correctly', () => {
    const run = createRun('run-1', '2024-01-01T00:00:00Z');
    expect(isLatestRun(run, [run])).toBe(true);
  });

  it('should handle runs with same timestamp', () => {
    const timestamp = '2024-01-01T00:00:00Z';
    const runs = [createRun('run-1', timestamp), createRun('run-2', timestamp)];

    // Both runs have the same timestamp, so both should be considered "latest"
    expect(isLatestRun(runs[0], runs)).toBe(true);
    expect(isLatestRun(runs[1], runs)).toBe(true);
  });

  it('should sort timestamps correctly (ISO 8601 format)', () => {
    const runs = [
      createRun('run-old', '2023-12-31T23:59:59Z'),
      createRun('run-new', '2024-01-01T00:00:00Z'),
    ];

    expect(isLatestRun(runs[1], runs)).toBe(true);
    expect(isLatestRun(runs[0], runs)).toBe(false);
  });
});
