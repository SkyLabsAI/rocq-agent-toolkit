import cn from 'classnames';
import { useAgentDetails } from '@/hooks/useAgentDetails';
import AgentRunsView from './AgentRunsView';
import { useEffect, useState } from 'react';
import { AgentSummary } from '@/types/types';
import { AgentSummaryTemp } from '@/services/dataservice';
import { Button } from '@/components/base';
import { Link } from 'react-router-dom';

interface AgentDetailsProps {
  agent: AgentSummary;
  activeAgent?: boolean;
  setActiveAgent: (agent: string) => void;
  agentDetailData: AgentSummaryTemp;
}

const AgentDetails: React.FC<AgentDetailsProps> = ({
  agent,
  activeAgent = false,
  setActiveAgent,
  agentDetailData,
}) => {
  const {
    loading,
    runDetails,
    isOpen,
    selectedRuns,
    toggleDetails,
    compareSelected,
    toggleRunSelection,
    clearSelectedRuns,
  } = useAgentDetails(agent.agent_name, setActiveAgent);

  useEffect(() => {
    if (!activeAgent) {
      clearSelectedRuns();
    }
  }, [activeAgent]);


  const [isSelected, setIsSelected] =useState<boolean>(false);
  

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
                {agentDetailData?.agentName?.charAt(0).toUpperCase()}
              </span>
            </div>
            <span className='truncate'>{agent.agent_name}</span>
          </div>
        </td>
        <td className='px-6 py-4 text-text font-medium'>
          <div className='flex items-center gap-3'>
            <div className='h-6   rounded-lg flex items-center justify-center'>
              <span className='text-text font-semibold text-sm'>
                {(agentDetailData?.successRate * 100).toPrecision(5)}%
              </span>
            </div>
          </div>
        </td>

        <td className='px-6 py-4 text-text font-medium'>
          <div className='flex items-center gap-3'>
            <div className='h-6   rounded-lg flex items-center justify-center'>
              <span className='text-text font-semibold text-sm'>
                {agentDetailData?.avgTime.toPrecision(5)}
              </span>
            </div>
          </div>
        </td>
        <td className='px-6 py-4 text-text font-medium'>
          <div className='flex items-center gap-3'>
            <div className='h-6   rounded-lg flex items-center justify-center'>
              <span className='text-text font-semibold text-sm'>
                {agentDetailData?.avgTokens.toPrecision(5)}
              </span>
            </div>
          </div>
        </td>
        <td className='px-6 py-4 text-text font-medium'>
          <div className='flex items-center gap-3'>
            <div className='h-6   rounded-lg flex items-center justify-center'>
              <span className='text-text font-semibold text-sm'>
                {agentDetailData?.avgLlmCalls.toPrecision(5)}
              </span>
            </div>
          </div>
        </td>
        <td className='px-6 py-4 text-text font-medium'>
          <div className='flex items-center gap-3 justify-center'>
           <Link to={"/compare/agents"} onClick={(e)=>{ e.stopPropagation()}}>
              <Button variant='default'  >
                Compare
              </Button>
           </Link>

          </div>
        </td>
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
              ) : (
                 runDetails.length === 0 
                ) ? (
                <div className='text-center py-8 text-text'>
                  No run details available.
                </div>
              ) : (
                <div className='space-y-4'>
                  <AgentRunsView
                    runDetails={runDetails}
                    agentName={agent.agent_name}
                    selectedRuns={selectedRuns}
                    toggleRunSelection={toggleRunSelection}
                    clearSelectedRuns={clearSelectedRuns}
                    tags={agentDetailData?.tags}
                    compareSelected={compareSelected}
                  />
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
