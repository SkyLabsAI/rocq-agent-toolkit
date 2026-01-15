import { useState } from 'react';

import { TagsDisplay } from '@/components/tags-display';
import { type AgentSummary } from '@/types/types';
import { cn } from '@/utils/cn';

import { DatasetAgentInstance } from './dataset-agent-instance';
import { useDatasetAgentClass } from './use-dataset-agent-class';

interface DatasetAgentClassProps {
  agent: AgentSummary;
  datasetId: string;
  isSelected: boolean;
  toggleSelection: () => void;
}

export const DatasetAgentClass: React.FC<DatasetAgentClassProps> = ({
  agent,
  datasetId,
}) => {
  const [isOpen, setIsOpen] = useState(false);
  const { instances, isLoading, fetchInstances } = useDatasetAgentClass(
    datasetId,
    agent.cls_checksum
  );

  const handleToggle = () => {
    const newIsOpen = !isOpen;
    setIsOpen(newIsOpen);
    if (newIsOpen && instances.length === 0) {
      fetchInstances();
    }
  };

  return (
    <>
      <tr
        className={cn(
          'hover:bg-white/5 cursor-pointer transition-colors duration-200'
        )}
        onClick={handleToggle}
        data-testid={`dataset-agent-card-${agent.cls_checksum}`}
      >
        <td className='px-6 py-2.5 text-text font-medium pl-16'>
          <div className='flex items-center gap-2.5'>
            <div className='w-0.5 h-5 bg-elevation-surface-overlay rounded-full' />
            <span className='truncate font-mono text-xs text-text-disabled'>
              {agent.cls_checksum.slice(0, 12)}
            </span>
          </div>
        </td>
      </tr>

      {isOpen && (
        <tr>
          <td colSpan={2}>
            <div className='px-6 py-2 pl-20'>
              {isLoading ? (
                <div className='flex items-center justify-center py-8'>
                  <div className='animate-spin rounded-full h-8 w-8 border-b-2 border-blue-400'></div>
                  <span className='ml-3 text-text'>
                    Loading agent instances...
                  </span>
                </div>
              ) : instances.length === 0 ? (
                <div className='text-center py-8 text-text'>
                  No agent instances available.
                </div>
              ) : (
                <div className='space-y-2'>
                  {instances.map(instance => (
                    <DatasetAgentInstance
                      key={instance.agent_checksum}
                      instance={instance}
                      datasetId={datasetId}
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
