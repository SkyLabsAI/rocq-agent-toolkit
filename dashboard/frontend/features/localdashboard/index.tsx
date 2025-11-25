'use client';

import React from 'react';
import { useSelectedRun } from '@/contexts/SelectedRunContext';
import Layout from '@/layouts/common';
import AgentDetails from './AgentDetails';
import { useLocalDashboard } from '@/hooks/useLocalDashboard';
import Button from '@/components/base/Button';
import RunDetailsView from '@/components/RunDetailsView';
import { RefreshIcon } from '@/icons/refresh';
import TaskDetailsModal from '../taskDetailsModal';
import AgentListIcon from '@/icons/agent-list';

const LocalDashboard: React.FC = () => {
  const {
    agentData,
    agentDetailData,
    isRefreshing,
    refreshMessage,
    handleRefresh,
    modalState,
    closeModal,
    openCodeModal,
  } = useLocalDashboard();
  const { selectedRun, setSelectedRun } = useSelectedRun();
  const [activeAgent, setActiveAgent] = React.useState<string | null>(null);

  return (
    <Layout title='Internal Dashboard'>
      {/* Refresh Message */}
      {refreshMessage && (
        <div className='mb-4 bg-elevation-surface-raised backdrop-blur-sm border border-elevation-surface-overlay rounded-xl p-4'>
          <p className='text-sm text-green-400'>{refreshMessage}</p>
        </div>
      )}
      {/* Main Table - only show when no run details are selected */}
      {!selectedRun && (
        <div className='backdrop-blur-sm border bg-elevation-surface border-elevation-surface-raised rounded-xl overflow-hidden'>
          <div className='px-6 py-4 border-b border-elevation-surface-raised flex items-center justify-between bg-elevation-surface-raised'>
            <div>
              <h2 className='text-[18px] font-semibold text-text leading-6'>
                Agent Performance
              </h2>
              <p className='text-text-subtlest text-[14px] mt-1 leading-5'>
                Click on any row to view detailed task information
              </p>
            </div>

            <div className='items-center flex gap-2'>
              <Button
                onClick={handleRefresh}
                disabled={isRefreshing}
                variant='default'
                leftIcon={
                  !isRefreshing ? (
                    <RefreshIcon className='h-5 w-5' />
                  ) : undefined
                }
              >
                {isRefreshing ? 'Refreshing...' : 'Refresh Data'}
              </Button>
            </div>
          </div>

          <div className=''>
            <table className='w-full text-left border-collapse'>
              <tbody className='divide-y divide-elevation-surface-overlay'>
                <tr className='text-text'>
                  <td>
                    <div className='flex gap-1 items-center px-6  text-[16px] py-5'>
                      <AgentListIcon className=' text-icon-success size-4' />
                      Agents
                    </div>
                  </td>
                  <td className='px-6 py-4 font-[16px] text-text-disabled'>
                    Success Rate
                  </td>
                  <td className='px-6 py-4 font-[16px] text-text-disabled'>
                    Avg Time (s)
                  </td>
                  <td className='px-6 py-4 font-[16px] text-text-disabled'>
                    Avg Tokens
                  </td>
                  <td className='px-6 py-4 font-[16px] text-text-disabled'>
                    Avg LLM Calls
                  </td>
                </tr>
                {agentData
                  .sort((a, b) => a.agent_name.localeCompare(b.agent_name))
                  .map((agent, index) => (
                    <AgentDetails
                      key={agent.agent_name}
                      agent={agent}
                      agentDetailData={agentDetailData[index]}
                      activeAgent={activeAgent === agent.agent_name}
                      setActiveAgent={setActiveAgent}
                    />
                  ))}
              </tbody>
            </table>
          </div>
        </div>
      )}
      {selectedRun && (
        <RunDetailsView
          run={selectedRun}
          onBack={() => setSelectedRun(null)}
          openCodeModal={openCodeModal}
        />
      )}

      <TaskDetailsModal
        isOpen={modalState.isOpen}
        onClose={closeModal}
        details={modalState.logs}
        title={
          modalState.selectedTask
            ? `Observability Logs - ${modalState.selectedTask.task_id}`
            : 'Task Logs'
        }
        taskId={modalState.selectedTask?.task_id}
      />
    </Layout>
  );
};

export default LocalDashboard;
