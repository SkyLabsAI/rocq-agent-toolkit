import React, { useState } from 'react';
import Button from '@/components/base/ui/button';
import { RefreshIcon } from '@/icons/refresh';
import SlidingTabs from '@/components/base/ui/sliding-tabs';
import AgentView from './agentview';
import DataView from './dataview';

type SortableKey = 'agent_name' | 'success_rate' | 'avg_cpu_time_sec' | 'avg_total_tokens' | 'avg_llm_invocation_count';

interface AgentTableProps {
  isRefreshing: boolean;
  handleRefresh: () => void;
}

const AgentTable: React.FC<AgentTableProps> = ({
  isRefreshing,
  handleRefresh,
}) => {


  const [activeTab, setActiveTab] = useState<'agents' | 'datasets'>('agents');

return   <div className='backdrop-blur-sm border bg-elevation-surface border-elevation-surface-raised rounded-xl overflow-hidden'>
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
          tabs={[{id:"agents", label:"Agents"},{id:"datasets", label:"Datasets"} ]}
          defaultTab='agents'
          onTabChange={(tabId) => setActiveTab(tabId as 'agents' | 'datasets')}
        />
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


    {activeTab === 'agents' && <AgentView/>}
    {activeTab === 'datasets' && <DataView/>}


    
  </div>
}

export default AgentTable;