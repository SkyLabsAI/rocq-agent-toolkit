import React, { Suspense } from 'react';
import { AgentSummary } from '@/types/types'; // adjust import as needed
import { AgentSummaryTemp } from '@/services/dataservice';
import { useLocalDashboard } from '@/hooks/useLocalDashboard';
import { useSearchParams } from 'react-router-dom';
import Layout from '@/layouts/common';
import { ComparePageContent } from '../runs-compare/compare-page-content';
import { CompareRunsHeader } from '../runs-compare/compare-page-content/compare-page-header';
import { RunsHeader } from '../runs-compare/compare-page-content/compare-page-summary/run-header';
import { TaskRow } from '../runs-compare/compare-page-content/compare-page-summary/run-row';

interface AgentCompareTableProps {
  allAgentSummaries: AgentSummaryTemp[];
  selectedAgents: string[];
}

const AgentCompareTable: React.FC = () => {
  const { agentDetailData } = useLocalDashboard();

  const [sp] = useSearchParams();

  const selectedAgents = sp.get('agents') || '';

  const agentsToCompare = agentDetailData.filter(agent =>
    selectedAgents.split(',').includes(agent.agentName)
  );
  return (
    // <div className='overflow-x-auto'>
    //   <table className='min-w-full border'>
    //     <thead>
    //       <tr>
    //         <th className='px-4 py-2'>Agent</th>
    //         <th className='px-4 py-2'>Success Rate</th>
    //         <th className='px-4 py-2'>Avg Time</th>
    //         <th className='px-4 py-2'>Avg Tokens</th>
    //         <th className='px-4 py-2'>Avg LLM Calls</th>
    //       </tr>
    //     </thead>
    //     <tbody>
    //       {agentsToCompare.map(agent => (
    //         <tr key={agent.agentName}>
    //           <td className='px-4 py-2'>{agent.agentName}</td>
    //           <td className='px-4 py-2'>
    //             {(agent.successRate * 100).toFixed(1)}%
    //           </td>
    //           <td className='px-4 py-2'>{agent.avgTime.toFixed(2)}</td>
    //           <td className='px-4 py-2'>{agent.avgTokens.toFixed(2)}</td>
    //           <td className='px-4 py-2'>{agent.avgLlmCalls.toFixed(2)}</td>
    //         </tr>
    //       ))}
    //     </tbody>
    //   </table>
    // </div>

    <Layout title='Compare Agents'>
      <div className='  text-text p-8 pt-0'>
        <div className='max-w-7xl mx-auto space-y-8'></div>
        <Suspense
          fallback={
            <div className='min-h-screen  text-text p-8'>
              <div className='max-w-7xl mx-auto'>
                <div className='flex items-center justify-center h-64'>
                  <div className='text-text-disabled'>
                    Loading comparison data...
                  </div>
                </div>
              </div>
            </div>
          }
        >
          </Suspense>
          <CompareRunsHeader title='Compare Agents' secondary={`Selected Agents: ${selectedAgents}`}/>

          <RunsHeader title="Agents" keys={["Tasks", "Success %", "Avg LLM Calls", "Avg Total Token", "Avg Exec Time (s)"]} />
          {agentsToCompare.map((agent)=><TaskRow  stats={[agent.agentName,agent.totalTasks, (agent.successRate * 100).toFixed(2), agent.avgLlmCalls, agent.avgTokens, agent.avgTime]} onClick={()=>{}}/>)}
         
        

      </div>
    </Layout>
  );
};

export default AgentCompareTable;
