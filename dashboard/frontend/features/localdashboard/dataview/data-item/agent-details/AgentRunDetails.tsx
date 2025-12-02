import React, { useState, useEffect } from 'react';
import { getRunDetails } from '@/services/dataservice';
import { RunDetailsResponse, TaskOutput } from '@/types/types';
import { Button } from '@/components/base';

interface AgentRunDetailsProps {
  runId: string;
  agentName: string;
  isExpanded: boolean;
}

const AgentRunDetails: React.FC<AgentRunDetailsProps> = ({
  runId,
  agentName,
  isExpanded,
}) => {
  const [runDetails, setRunDetails] = useState<RunDetailsResponse | null>(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    if (isExpanded && !runDetails) {
      fetchRunDetails();
    }
  }, [isExpanded, runId]);

  const fetchRunDetails = async () => {
    try {
      setLoading(true);
      setError(null);
      const details = await getRunDetails([runId]);
      setRunDetails(details[0]);
    } catch (err) {
      console.error('Error fetching run details:', err);
      setError(err instanceof Error ? err.message : 'Failed to fetch run details');
    } finally {
      setLoading(false);
    }
  };

  const getStatusColor = (status: string) => {
    switch (status.toLowerCase()) {
      case 'success':
        return 'text-green-400 bg-green-400/10';
      case 'failure':
        return 'text-red-400 bg-red-400/10';
      default:
        return 'text-gray-400 bg-gray-400/10';
    }
  };

  const formatMetricValue = (value: number, unit?: string) => {
    if (value < 1000) {
      return `${value.toFixed(2)}${unit ? ` ${unit}` : ''}`;
    }
    return `${(value / 1000).toFixed(2)}K${unit ? ` ${unit}` : ''}`;
  };

  if (!isExpanded) return null;

  return (
    <tr>
      <td colSpan={6}>
        <div className='px-8 pt-4 pb-9 bg-elevation-surface rounded-lg '>
          {loading && (
            <div className="flex items-center justify-center py-8">
              <div className="animate-spin rounded-full h-8 w-8 border-b-2 border-primary"></div>
              <span className="ml-3 text-text-secondary">Loading run details...</span>
            </div>
          )}

          {error && (
            <div className="bg-red-500/10 border border-red-500/20 rounded-lg p-4">
              <div className="text-red-400 font-medium">Error loading run details</div>
              <div className="text-red-300 text-sm mt-1">{error}</div>
            </div>
          )}

          {runDetails && !loading && (
            <div className="space-y-4">
              {/* Header */}
              <div className="grid grid-cols-6 gap-4">
                <div className="text-text text-[16px]">Tasks</div>
                <div className="text-text-disabled text-[14px]">Status</div>
                <div className="text-text-disabled text-[14px]">LLM Calls</div>
                <div className="text-text-disabled text-[14px]">Total Tokens</div>
                <div className="text-text-disabled text-[14px]">Execution Time</div>
                <div className="text-text-disabled text-[14px]"></div>
              </div>
              
              {/* Rows */}
              <div className="flex flex-col gap-2 justify-between">
                {runDetails.tasks.map((task: TaskOutput) => (
                  <div key={task.task_id} className="grid grid-cols-6 gap-4 p-2.5 bg-elevation-surface-raised rounded items-center">
                    <div className="text-text">{task.task_id}</div>
                    <div>
                      <span className={`px-2 py-1 rounded text-xs font-medium ${task.status === 'Success' ? 'text-green-400' : 'text-red-400'}`}>
                        {task.status}
                      </span>
                    </div>
                    <div className="text-text">{task.metrics.llm_invocation_count}</div>
                    <div className="text-text">{formatMetricValue(task.metrics.token_counts.total_tokens)}</div>
                    <div className="text-text">{task.metrics.resource_usage.execution_time_sec.toFixed(2)}s</div>
                    <div >
                      <Button className='float-right' >
                        View Logs
                      </Button>
                    </div>
                  </div>
                ))}
              </div>
            </div>
          )}
        </div>
      </td>
    </tr>
  );
};

export default AgentRunDetails;