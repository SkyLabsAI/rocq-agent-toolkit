import cn from 'classnames';

import { useAgentInstances } from '@/hooks/use-agent-instances';
import { useBenchmarks } from '@/hooks/use-dataview';
import { type AgentSummary } from '@/types/types';

import { AgentInstance } from './agent-instances';

interface AgentDetailsProps {
  agent: AgentSummary;
}

const AgentDetails: React.FC<AgentDetailsProps> = ({ agent }) => {
  const { instances, isLoading, isOpen, toggleDetails } = useAgentInstances(
    agent.cls_checksum
  );

  const { benchmarks } = useBenchmarks();

  return (
    <>
      <tr
        className={cn(
          'hover:bg-white/5 cursor-pointer transition-colors duration-200'
        )}
        onClick={toggleDetails}
        data-testid={`agent-row-${agent.cls_checksum}`}
      >
        <td className='px-6 py-2.5 text-text font-medium pl-16'>
          <div className='flex items-center gap-2.5'>
            <div className='w-0.5 h-5 bg-elevation-surface-overlay rounded-full' />
            <span
              className='truncate font-mono text-xs text-text-disabled'
              data-testid='agent-name'
            >
              {agent.cls_checksum.slice(0, 12)}
            </span>
          </div>
        </td>
      </tr>

      {isOpen && (
        <tr data-testid={`agent-expanded-${agent.cls_checksum}`}>
          <td colSpan={2}>
            <div
              className='px-6 py-2 pl-20'
              data-testid='agent-expanded-content'
            >
              {isLoading ? (
                <div
                  className='flex items-center justify-center py-8'
                  data-testid='agent-loading'
                >
                  <div className='animate-spin rounded-full h-8 w-8 border-b-2 border-blue-400'></div>
                  <span className='ml-3 text-text'>
                    Loading agent instances...
                  </span>
                </div>
              ) : instances.length === 0 ? (
                <div
                  className='text-center py-8 text-text'
                  data-testid='agent-no-instances'
                >
                  No agent instances available.
                </div>
              ) : (
                <div className='space-y-2'>
                  {instances.map(instance => (
                    <AgentInstance
                      key={instance.agent_checksum}
                      instance={instance}
                      benchmarks={benchmarks}
                    />
                  ))}
                </div>
              )}
            </div>
          </td>
        </tr>
      )}
    </>
  );
};

export default AgentDetails;
