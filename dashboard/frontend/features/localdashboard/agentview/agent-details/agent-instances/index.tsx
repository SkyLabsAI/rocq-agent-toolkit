import { useState } from 'react';

import { TagsDisplay } from '@/components/tags-display';
import { ChevronUpIcon } from '@/icons/chevron-up';
import { type AgentInstanceSummary, type Benchmark } from '@/types/types';
import { cn } from '@/utils/cn';

import { InstanceBenchmarks } from './instance-benchmarks';
import { useAgentInstance } from './use-agent-instance';

interface AgentInstanceProps {
  instance: AgentInstanceSummary;
  benchmarks: Benchmark[];
}

export const AgentInstance: React.FC<AgentInstanceProps> = ({
  instance,
  benchmarks,
}) => {
  const [isOpen, setIsOpen] = useState(false);
  const { isLoading } = useAgentInstance(instance.agent_checksum);

  const handleToggle = () => {
    setIsOpen(!isOpen);
  };

  return (
    <div
      className='border-l-4 border-background-warning/40 ml-6 mb-3 rounded-r-md overflow-hidden'
      data-testid={`instance-card-${instance.agent_checksum}`}
    >
      <div
        className='bg-elevation-surface-raised/80 hover:bg-elevation-surface-raised overflow-hidden py-3.5 px-5 flex justify-between items-center cursor-pointer transition-colors border-l-0'
        onClick={handleToggle}
      >
        <div className='flex gap-3 items-center text-text min-w-0 shrink'>
          <ChevronUpIcon
            className={cn('size-4 text-text-disabled shrink-0', {
              'rotate-180': isOpen,
            })}
          />
          <div className='flex items-center gap-2.5 min-w-0'>
            <div className='h-5 w-5 bg-background-warning rounded flex items-center justify-center shrink-0'>
              <span className='text-text-warning font-semibold text-xs'>
                {instance.name.charAt(0).toUpperCase()}
              </span>
            </div>
            <div className='flex flex-col min-w-0'>
              <div className='flex items-center gap-2'>
                <span className='text-xs font-medium text-text-disabled uppercase tracking-wide'>
                  Instance
                </span>
                <span
                  className='text-[13px] font-medium truncate text-text'
                  data-testid='instance-name'
                >
                  {instance.name}@{instance.agent_checksum.slice(0, 12)}
                </span>
              </div>
            </div>
          </div>
        </div>

        <div className='flex items-center gap-4 shrink-0'>
          <div className='flex items-center gap-3 text-xs text-text-disabled bg-elevation-surface-overlay px-3 py-1.5 rounded-md'>
            <div className='flex items-center gap-1.5'>
              <span className='font-medium text-text'>
                {instance.total_runs}
              </span>
              <span>runs</span>
            </div>
            <span>·</span>
            <div className='flex items-center gap-1.5'>
              <span className='font-medium text-text'>{benchmarks.length}</span>
              <span>datasets</span>
            </div>
          </div>
        </div>
      </div>

      {isOpen && (
        <div className='pl-4' data-testid='instance-expanded-content'>
          {isLoading ? (
            <div
              className='flex justify-center p-4'
              data-testid='instance-loading'
            >
              <div className='animate-spin rounded-full h-6 w-6 border-b-2 border-blue-400'></div>
            </div>
          ) : benchmarks.length === 0 ? (
            <div
              className='text-center py-6 text-text-disabled text-sm'
              data-testid='instance-no-datasets'
            >
              No datasets available for this instance.
            </div>
          ) : (
            <div className='space-y-1'>
              {benchmarks.map(benchmark => (
                <InstanceBenchmarks
                  key={benchmark.dataset_id}
                  benchmark={benchmark}
                  instanceChecksum={instance.agent_checksum}
                  instanceName={instance.name}
                />
              ))}
            </div>
          )}
        </div>
      )}
    </div>
  );
};
