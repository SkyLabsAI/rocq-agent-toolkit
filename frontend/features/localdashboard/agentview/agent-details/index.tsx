import cn from 'classnames';
import { useAgentDetails } from '@/hooks/useAgentDetails';
import AgentRunsView from '../../AgentRunsView';
import { useEffect, useState } from 'react';
import { AgentSummary, Run } from '@/types/types';
import { AgentSummaryTemp } from '@/services/dataservice';
import { Button } from '@/components/base';
import { ChevronUpIcon } from '@/icons/chevron-up';
import { AgentBenchmark } from './agent-benchmarks';
import { useBenchmarks } from '@/hooks/use-dataview';

interface AgentDetailsProps {
  agent: AgentSummary;
  activeAgent?: boolean;
  setActiveAgent: (agent: string) => void;
  agentDetailData: AgentSummaryTemp;
  isSelected: boolean;
  toggleSelection: () => void;
  selectedRuns: string[];
  toggleRunSelection: (run: Run) => void;
  clearSelectedRuns: () => void;
  compareSelectedRuns: () => void;
}

const AgentDetails: React.FC<AgentDetailsProps> = ({
  agent,
  agentDetailData,
  isSelected,
  toggleSelection,
  selectedRuns,
  toggleRunSelection,
  clearSelectedRuns,
  compareSelectedRuns,
}) => {
  const { loading, runDetails, isOpen, toggleDetails } = useAgentDetails(
    agent.agent_name
  );

  const {benchmarks} = useBenchmarks();


  return (
    <>
      <tr
        className={cn(
          'hover:bg-white/5 cursor-pointer transition-colors duration-200'
        )}
        onClick={toggleDetails}
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
        {/* <td className='px-6 py-4 text-text font-medium'>
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
        </td> */}
      </tr>

      {isOpen && (
        <tr>
          <td colSpan={7}>
            <div className='px-6'>
              {loading ? (
                <div className='flex items-center justify-center py-8'>
                  <div className='animate-spin rounded-full h-8 w-8 border-b-2 border-blue-400'></div>
                  <span className='ml-3 text-text'>
                    Loading task details...
                  </span>
                </div>
              ) : runDetails.length === 0 ? (
                <div className='text-center py-8 text-text'>
                  No run details available.
                </div>
              ) :
                benchmarks.map((benchmark) => (<AgentBenchmark key={benchmark.dataset_id} benchmark={benchmark} agentName={agent.agent_name} />))
                
              }
            </div>
          </td>
        </tr>
      )}
    </>
  );
};

export default AgentDetails;
