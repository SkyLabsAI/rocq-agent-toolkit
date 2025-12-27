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
      className='border-l-2 border-elevation-surface-overlay ml-6'
      data-testid={`instance-card-${instance.agent_checksum}`}
    >
      <div
        className='bg-elevation-surface-raised hover:bg-white/5 overflow-hidden py-4 px-6 flex justify-between items-center cursor-pointer transition-colors'
        onClick={handleToggle}
      >
        <div className='flex gap-2 items-center text-text'>
          <ChevronUpIcon
            className={cn('size-5 text-text-disabled', {
              'rotate-180': isOpen,
            })}
          />
          <div className='flex items-center gap-3'>
            <div className='h-6 w-6 bg-background-warning rounded-lg flex items-center justify-center'>
              <span className='text-text-warning font-semibold text-sm'>
                {instance.name.charAt(0).toUpperCase()}
              </span>
            </div>
            <span
              className='text-[15px] font-medium'
              data-testid='instance-name'
            >
              {instance.name}
            </span>
          </div>
        </div>

        <div className='flex gap-6 text-sm'>
          <div className='flex flex-col items-end'>
            <span className='text-text-disabled text-xs'>Success Rate</span>
            <span className='text-text font-medium'>
              {((instance.best_run?.success_rate ?? 0) * 100).toFixed(2)}%
            </span>
          </div>
          <div className='flex flex-col items-end'>
            <span className='text-text-disabled text-xs'>Avg Time</span>
            <span className='text-text font-medium'>
              {(instance.best_run?.avg_cpu_time_sec ?? 0).toFixed(2)}s
            </span>
          </div>
          <div className='flex flex-col items-end'>
            <span className='text-text-disabled text-xs'>Avg Tokens</span>
            <span className='text-text font-medium'>
              {(instance.best_run?.avg_total_tokens ?? 0).toFixed(0)}
            </span>
          </div>
          <div className='flex flex-col items-end'>
            <span className='text-text-disabled text-xs'>Total Runs</span>
            <span className='text-text font-medium'>{instance.total_runs}</span>
          </div>
        </div>
      </div>

      {isOpen && (
        <div className='pl-6' data-testid='instance-expanded-content'>
          {isLoading ? (
            <div
              className='flex justify-center p-4'
              data-testid='instance-loading'
            >
              <div className='animate-spin rounded-full h-8 w-8 border-b-2 border-blue-400'></div>
            </div>
          ) : benchmarks.length === 0 ? (
            <div
              className='text-center py-8 text-text'
              data-testid='instance-no-datasets'
            >
              No datasets available for this instance.
            </div>
          ) : (
            benchmarks.map(benchmark => (
              <InstanceBenchmarks
                key={benchmark.dataset_id}
                benchmark={benchmark}
                instanceChecksum={instance.agent_checksum}
                instanceName={instance.name}
              />
            ))
          )}
        </div>
      )}
    </div>
  );
};
