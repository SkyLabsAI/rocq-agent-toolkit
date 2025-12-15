import cn from 'classnames';

import { useAgentDetails } from '@/hooks/use-agent-details';
import { useBenchmarks } from '@/hooks/use-dataview';
import { type AgentSummary } from '@/types/types';

import { AgentBenchmark } from './agent-benchmarks';

interface AgentDetailsProps {
  agent: AgentSummary;
}

const AgentDetails: React.FC<AgentDetailsProps> = ({ agent }) => {
  const { loading, runDetails, isOpen, toggleDetails } = useAgentDetails(
    agent.agent_name
  );

  const { benchmarks } = useBenchmarks();

  return (
    <>
      <tr
        className={cn(
          'hover:bg-white/5 cursor-pointer transition-colors duration-200'
        )}
        onClick={toggleDetails}
        data-testid={`agent-row-${agent.agent_name}`}
      >
        <td className='px-6 py-4 text-text font-medium'>
          <div className='flex items-center gap-3'>
            <div className='h-6 w-6 bg-background-information rounded-lg flex items-center justify-center'>
              <span className='text-text-information font-semibold text-sm'>
                {agent.agent_name.charAt(0).toUpperCase()}
              </span>
            </div>
            <span className='truncate' data-testid='agent-name'>
              {agent.agent_name}
            </span>
          </div>
        </td>
        <td className='px-6 py-4 text-text font-medium'>
          <div className='flex items-center gap-3'>
            <div className='h-6   rounded-lg flex items-center justify-center'>
              <span className='text-text font-semibold text-sm'>
                {((agent.best_run?.success_rate ?? 0) * 100).toFixed(2)}%
              </span>
            </div>
          </div>
        </td>

        <td className='px-6 py-4 text-text font-medium'>
          <div className='flex items-center gap-3'>
            <div className='h-6   rounded-lg flex items-center justify-center'>
              <span className='text-text font-semibold text-sm'>
                {(agent.best_run?.avg_cpu_time_sec ?? 0).toFixed(2)}
              </span>
            </div>
          </div>
        </td>
        <td className='px-6 py-4 text-text font-medium'>
          <div className='flex items-center gap-3'>
            <div className='h-6   rounded-lg flex items-center justify-center'>
              <span className='text-text font-semibold text-sm'>
                {(agent.best_run?.avg_total_tokens ?? 0).toFixed(2)}
              </span>
            </div>
          </div>
        </td>
        <td className='px-6 py-4 text-text font-medium'>
          <div className='flex items-center gap-3'>
            <div className='h-6   rounded-lg flex items-center justify-center'>
              <span className='text-text font-semibold text-sm'>
                {(agent.best_run?.avg_llm_invocation_count ?? 0).toFixed(2)}
              </span>
            </div>
          </div>
        </td>
      </tr>

      {isOpen && (
        <tr data-testid={`agent-expanded-${agent.agent_name}`}>
          <td colSpan={7}>
            <div className='px-6' data-testid='agent-expanded-content'>
              {loading ? (
                <div
                  className='flex items-center justify-center py-8'
                  data-testid='agent-loading'
                >
                  <div className='animate-spin rounded-full h-8 w-8 border-b-2 border-blue-400'></div>
                  <span className='ml-3 text-text'>
                    Loading task details...
                  </span>
                </div>
              ) : runDetails.length === 0 ? (
                <div
                  className='text-center py-8 text-text'
                  data-testid='agent-no-details'
                >
                  No run details available.
                </div>
              ) : (
                benchmarks.map(benchmark => (
                  <AgentBenchmark
                    key={benchmark.dataset_id}
                    benchmark={benchmark}
                    agentName={agent.agent_name}
                  />
                ))
              )}
            </div>
          </td>
        </tr>
      )}
    </>
  );
};

export default AgentDetails;
