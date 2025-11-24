'use client';

import React from 'react';
import {
  SelectedRunProvider,
  useSelectedRun,
} from '@/contexts/SelectedRunContext';
import Layout from '@/layouts/common';
import AgentDetails from '../leaderboard/agentDetails';
import { useAdminDashboard } from '@/hooks/useAdminDashboard';
import Button from '@/components/base/Button';
import RunDetailsView from '@/components/RunDetailsView';
import { RefreshIcon } from '@/icons/refresh';
import TaskDetailsModal from '../taskDetailsModal';

const AdminDashboard: React.FC = () => {
  const {
    agentData,
    isRefreshing,
    refreshMessage,
    handleRefresh,
    modalState,
    closeModal,
    openCodeModal,
  } = useAdminDashboard();
  const { selectedRun, setSelectedRun } = useSelectedRun();
  const [activeAgent, setActiveAgent] = React.useState<string | null>(null);

  return (
    <Layout title='Internal Dashboard'>
      {/* Refresh Message */}
      {refreshMessage && (
        <div className='mb-4 bg-white/5 backdrop-blur-sm border border-white/10 rounded-xl p-4'>
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
                {agentData.sort((a, b) => a.agent_name.localeCompare(b.agent_name)).map(agent => (
                  <AgentDetails
                    key={agent.agent_name}
                    agent_name={agent.agent_name}
                    adminView
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

export default AdminDashboard;
