import { useState } from 'react';

import { Button } from '@/components/base';
import { type AgentSummary } from '@/types/types';
import { cn } from '@/utils/cn';

import { DatasetAgentInstance } from './dataset-agent-instance';
import { useDatasetAgentClass } from './use-dataset-agent-class';
import { TagsDisplay } from '@/components/tags-display';

interface DatasetAgentClassProps {
  agent: AgentSummary;
  datasetId: string;
  isSelected: boolean;
  toggleSelection: () => void;
}

export const DatasetAgentClass: React.FC<DatasetAgentClassProps> = ({
  agent,
  datasetId,
  isSelected,
  toggleSelection,
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
      >
        <td className='px-6 py-4 text-text font-medium'>
          <div className='flex items-center gap-3'>
            <div className='h-6 w-6 bg-background-information rounded-lg flex items-center justify-center'>
              <span className='text-text-information font-semibold text-sm'>
                {agent.cls_name.charAt(0).toUpperCase()}
              </span>
            </div>
            <span className='truncate'>{agent.cls_name}</span>
          </div>
        </td>
        <td>
          <TagsDisplay
            tags={agent.cls_provenance as Record<string, string>}
            modalTitle={`All Tags for ${agent.cls_name}`}
          />
        </td>
      </tr>

      {isOpen && (
        <tr>
          <td colSpan={7}>
            <div className='px-6 py-4'>
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
