import { useState } from 'react';

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
      className='border-l-2 border-background-warning/30 ml-8 mb-2 rounded-r-md overflow-hidden'
      data-testid={`instance-card-${instance.agent_checksum}`}
    >
      <div
        className='bg-elevation-surface-raised/60 hover:bg-elevation-surface-raised/80 overflow-hidden py-2.5 px-4 flex justify-between items-center cursor-pointer transition-colors border-l-0'
        onClick={handleToggle}
      >
        <div className='flex gap-2 items-center text-text min-w-0 shrink'>
          <ChevronUpIcon
            className={cn('size-3.5 text-text-disabled shrink-0', {
              'rotate-180': isOpen,
            })}
          />
          <div className='flex items-center gap-2 min-w-0'>
            <div className='h-4 w-4 bg-background-warning rounded flex items-center justify-center shrink-0'>
              <span className='text-text-warning font-semibold text-[10px]'>
                {instance.name.charAt(0).toUpperCase()}
              </span>
            </div>
            <span
              className='text-sm font-medium truncate text-text'
              data-testid='instance-name'
            >
              {instance.name}@{instance.agent_checksum}
            </span>
          </div>
        </div>

        <div className='flex items-center gap-2 shrink-0'>
          <div className='flex items-center gap-2.5 text-xs text-text-disabled bg-elevation-surface-overlay px-2.5 py-1 rounded-md'>
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
