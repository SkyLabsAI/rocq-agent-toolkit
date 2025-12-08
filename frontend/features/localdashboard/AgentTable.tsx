import React, { useState } from 'react';
import Button from '@/components/base/ui/button';
import { RefreshIcon } from '@/icons/refresh';
import SlidingTabs from '@/components/base/ui/sliding-tabs';
import AgentView from './agentview';
import DataView from './dataview';
import AgentListIcon from '@/icons/agent-list';
import { DataSetListIcon } from '@/icons/dataset-list';



const AgentTable: React.FC = () => {
  const [activeTab, setActiveTab] = useState<'agents' | 'datasets'>('agents');

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
                id: 'agents',
                label: 'Agents',
                icon: <AgentListIcon className='size-[15px]' />,
              },
              {
                id: 'datasets',
                label: 'Datasets',
                icon: <DataSetListIcon className='size-[15px]' />,
              },
            ]}
            defaultTab='agents'
            onTabChange={tabId => setActiveTab(tabId as 'agents' | 'datasets')}
          />
          <Button
            onClick={() => window.location.reload()}
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
    </div>
  );
};

export default AgentTable;
