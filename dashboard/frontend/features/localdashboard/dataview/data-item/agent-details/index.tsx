import cn from 'classnames';
import { AgentSummary } from '@/types/types';
import { Button } from '@/components/base';
import { useState } from 'react';
import AgentRunDetails from './AgentRunDetails';

interface AgentDetailsProps {
  agent: AgentSummary;
  isSelected: boolean;
  toggleSelection: () => void;
}

const AgentDetails: React.FC<AgentDetailsProps> = ({
  agent,
  isSelected,
  toggleSelection,
}) => {
  const [isExpanded, setIsExpanded] = useState(false);

  const toggleExpanded = () => {
    setIsExpanded(!isExpanded);
  };

  return (
    <>
      <tr
        className={cn(
          'hover:bg-white/5 cursor-pointer transition-colors duration-200',
          isExpanded && 'bg-white/5'
        )}
        onClick={toggleExpanded}
      >
        <td className='px-6 py-4 text-text font-medium'>
          <div className='flex items-center gap-3'>
            <div className='h-6 w-6 bg-background-information rounded-lg flex items-center justify-center'>
              <span className='text-text-information font-semibold text-sm'>
                {agent.agent_name.charAt(0).toUpperCase()}
              </span>
            </div>
            <span className='truncate'>{agent.agent_name}</span>
          </div>
        </td>
        <td className='px-6 py-4 text-text font-medium'>
          <div className='flex items-center gap-3'>
            <div className='h-6   rounded-lg flex items-center justify-center'>
              <span className='text-text font-semibold text-sm'>
                {((agent.best_run?.success_rate ?? 0)*100).toFixed(2)}%
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
        <td className='px-6 py-4 text-text font-medium'>
          <div className='flex items-center gap-3 justify-center'>
          

            <Button
              variant={isSelected ? 'danger' : 'default'}
              onClick={e => {
             e.stopPropagation();
                toggleSelection();
              }}
              className='text-sm whitespace-nowrap text-[14px] font-normal float-end w-[100px] flex justify-center'
            >
              {isSelected ? 'Deselect' : 'Compare'}
            </Button>
        
          </div>
        </td>
      </tr>
      
      {/* Agent Run Details - only render if agent has a best_run */}
      {agent.best_run && isExpanded && (
        <AgentRunDetails
          runId={agent.best_run.run_id}
          agentName={agent.agent_name}
          isExpanded={isExpanded}
        />
      )}
    </>
  );
};

export default AgentDetails;
