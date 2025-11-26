import React, { Suspense } from 'react';
import { AgentSummary } from '@/types/types'; // adjust import as needed
import { AgentSummaryTemp } from '@/services/dataservice';
import { useLocalDashboard } from '@/hooks/useLocalDashboard';
import { useSearchParams } from 'react-router-dom';
import Layout from '@/layouts/common';
import { ComparePageContent } from '../runs-compare/compare-page-content';

interface AgentCompareTableProps {
  allAgentSummaries: AgentSummaryTemp[];
  selectedAgents: string[];
}

const AgentCompareTable: React.FC = () => {
  const { agentDetailData } = useLocalDashboard();

  const [sp] = useSearchParams();

  const selectedAgents = sp.get('selectedAgents') || '';

  const agentsToCompare = agentDetailData
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
          <ComparePageContent />
        </Suspense>
      </div>
    </Layout>
  );
};

export default AgentCompareTable;
