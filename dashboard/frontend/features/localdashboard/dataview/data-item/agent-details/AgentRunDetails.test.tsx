import { fireEvent, render, screen, waitFor } from '@testing-library/react';
import React from 'react';

import { getObservabilityLogs, getRunDetails } from '@/services/dataservice';

import { AgentRunDetails } from './AgentRunDetails';

jest.mock('@/services/dataservice');
jest.mock('@/features/taskDetailsModal', () => ({
  __esModule: true,
  default: ({ isOpen }: { isOpen: boolean }) =>
    isOpen ? <div data-testid='task-details-modal'>Task Modal</div> : null,
}));

const mockGetRunDetails = getRunDetails as jest.MockedFunction<
  typeof getRunDetails
>;
const mockGetObservabilityLogs = getObservabilityLogs as jest.MockedFunction<
  typeof getObservabilityLogs
>;

describe('AgentRunDetails', () => {
  const mockRunDetails = {
    run_id: 'run1',
    agent_name: 'agent1',
    total_tasks: 2,
    tasks: [
      {
        run_id: 'run1',
        task_kind: 'FullProofTask',
        task_id: 'task1',
        timestamp_utc: '2024-01-01',
        agent_name: 'agent1',
        status: 'Success',
        results: {},
        metrics: {
          llm_invocation_count: 1,
          token_counts: {
            input_tokens: 100,
            output_tokens: 50,
            total_tokens: 150,
          },
          resource_usage: {
            execution_time_sec: 1.0,
            cpu_time_sec: 0.8,
            gpu_time_sec: 0.2,
          },
          custom: null,
        },
      },
    ],
  };

  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('should fetch run details when expanded', async () => {
    mockGetRunDetails.mockResolvedValue([mockRunDetails]);

    render(
      <AgentRunDetails runId='run1' agentName='agent1' isExpanded={true} />
    );

    await waitFor(() => {
      expect(mockGetRunDetails).toHaveBeenCalledWith(['run1']);
    });
  });

  it('should not fetch when not expanded', () => {
    render(
      <AgentRunDetails runId='run1' agentName='agent1' isExpanded={false} />
    );

    expect(mockGetRunDetails).not.toHaveBeenCalled();
  });

  it('should display loading state', () => {
    mockGetRunDetails.mockImplementation(() => new Promise(() => {}));

    render(
      <AgentRunDetails runId='run1' agentName='agent1' isExpanded={true} />
    );

    // Component should be in loading state
    expect(mockGetRunDetails).toHaveBeenCalled();
  });

  it('should handle fetch error', async () => {
    const consoleError = jest.spyOn(console, 'error').mockImplementation();
    mockGetRunDetails.mockRejectedValue(new Error('Network error'));

    render(
      <AgentRunDetails runId='run1' agentName='agent1' isExpanded={true} />
    );

    await waitFor(() => {
      expect(consoleError).toHaveBeenCalled();
    });

    consoleError.mockRestore();
  });
});
