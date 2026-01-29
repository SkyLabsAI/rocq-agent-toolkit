import { useSearchParams } from 'next/navigation';
import React, { useEffect, useState } from 'react';

import Button from '@/components/base/ui/button';
import SlidingTabs from '@/components/base/ui/sliding-tabs';
import AgentListIcon from '@/icons/agent-list';
import { DataSetListIcon } from '@/icons/dataset-list';
import { ProjectListIcon } from '@/icons/project-list';
import { RefreshIcon } from '@/icons/refresh';

import AgentView from './agentview';
import DataView from './dataview';
import TaskSetView from './projectview';

const AgentTable: React.FC = () => {
  const searchParams = useSearchParams();

  // Initialize from URL params or default
  const initialTab =
    (searchParams.get('view') as 'agents' | 'datasets' | 'tasksets') ||
    'tasksets';
  const [activeTab, setActiveTab] = useState<
    'agents' | 'datasets' | 'tasksets'
  >(initialTab);

  // Update URL when tab changes (without page refresh)
  useEffect(() => {
    const params = new URLSearchParams(window.location.search);
    if (activeTab === 'tasksets') {
      params.delete('view');
    } else {
      params.set('view', activeTab);
    }
    const newUrl = params.toString()
      ? `?${params.toString()}`
      : window.location.pathname;
    window.history.replaceState({}, '', newUrl);
  }, [activeTab]);

  return (
    <div className='backdrop-blur-sm border bg-elevation-surface border-elevation-surface-raised rounded-xl overflow-hidden'>
      <div className='px-6 py-4 border-b border-elevation-surface-raised flex items-center justify-between bg-elevation-surface-raised'>
        <div>
          <h2 className='text-[18px] font-semibold text-text leading-6'>
            Leader Dashboard
          </h2>
          <p className='text-text-subtlest text-[14px] mt-1 leading-5'>
            Click on any row to get detailed information
          </p>
        </div>

        <div className='items-center flex gap-2'>
          <SlidingTabs
            tabs={[
              {
                id: 'tasksets',
                label: 'Tasks',
                icon: <ProjectListIcon className='size-[15px]' />,
              },
              {
                id: 'agents',
                label: 'Agents',
                icon: <AgentListIcon className='size-[15px]' />,
              },
              {
                id: 'datasets',
                label: 'Projects',
                icon: <DataSetListIcon className='size-[15px]' />,
              },
            ]}
            defaultTab={initialTab}
            onTabChange={tabId =>
              setActiveTab(tabId as 'agents' | 'datasets' | 'tasksets')
            }
          />
          <Button
            onClick={() => router.push('/')}
            disabled={false}
            variant='default'
            leftIcon={<RefreshIcon className='h-5 w-5' />}
          >
            Refresh Data
          </Button>
        </div>
      </div>

      {activeTab === 'agents' && <AgentView />}
      {activeTab === 'datasets' && <DataView />}
      {activeTab === 'tasksets' && <TaskSetView />}
    </div>
  );
};

export default AgentTable;
