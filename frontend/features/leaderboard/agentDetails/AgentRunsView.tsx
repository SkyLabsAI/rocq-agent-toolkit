'use client'

import React from 'react';
import { Run, useSelectedRun } from '@/contexts/SelectedRunContext';
import RunRow from '@/components/RunRow';
import StickyCompareBar from '@/components/StickyCompareBar';
import { PlayIcon } from '@/icons/play';

type AgentRunsViewProps = {
  runDetails: any[];
  agentName: string;
  selectedRuns: string[];
  toggleRunSelection: (run: Run) => void;
  clearSelectedRuns: () => void;
  compareSelected: () => void;
};

const AgentRunsView: React.FC<AgentRunsViewProps> = ({
  runDetails,
  agentName,
  selectedRuns,
  toggleRunSelection,
  clearSelectedRuns,
  compareSelected,
}) => {
  const { setSelectedRun } = useSelectedRun();

  const loadPinnedRuns = (agentName: string): Set<string> => {
    try {
      const key = `pinnedRuns-${agentName}`;
      const stored = localStorage.getItem(key);
      return stored ? new Set(JSON.parse(stored)) : new Set();
    } catch (error) {
      console.error('Error loading pinned runs from localStorage:', error);
      return new Set();
    }
  };

  const [pinnedRuns, setPinnedRuns] = React.useState<Set<string>>(() => loadPinnedRuns(agentName));

  // Save pinned runs to localStorage whenever it changes
  React.useEffect(() => {
    try {
      const key = `pinnedRuns-${agentName}`;
      localStorage.setItem(key, JSON.stringify(Array.from(pinnedRuns)));
    } catch (error) {
      console.error('Error saving pinned runs to localStorage:', error);
    }
  }, [pinnedRuns, agentName]);


  const handleRunClick = (run: Run) => {
    setSelectedRun(run);
  };

  const handleBackToRuns = () => {
    setSelectedRun(null);
  };

  const toggleOnPin = (run: Run) => {
    setPinnedRuns((prev) => {
      const newSet = new Set(prev);
      if (newSet.has(run.run_id)) {
        newSet.delete(run.run_id);
      } else {
        newSet.add(run.run_id);
      }
      return newSet;
    });
  };

  return (
    <div className='space-y-4 relative '>
      {/* Header using CSS Grid with fractional units for perfect alignment */}
      <div className='grid grid-cols-[3fr_1fr_1fr_1fr_1.2fr_auto] gap-4 items-center mt-4 mb-3  z-20'>
        <div className='flex gap-1 items-center'>
          <PlayIcon />
          <h3 className='text-[16px] leading-4 font-semibold text-text'>Runs</h3>
        </div>

        <div>
          <p className='font-noto-sans font-normal leading-5 text-text-disabled text-sm'>
            Total Tasks
          </p>
        </div>

        <div>
          <p className='font-noto-sans font-normal leading-5 text-text-disabled text-sm'>
            Success Rate
          </p>
        </div>

        <div>
          <p className='font-noto-sans font-normal leading-5 text-text-disabled text-sm'>
            Timestamp
          </p>
        </div>

        <div>
          {/* Invisible button to match content row button dimensions */}
          <div className='bg-transparent relative rounded border border-transparent opacity-0 pointer-events-none'>
           
          </div>
        </div>
      </div>

      {/* Admin view: Runs list with selectable compare actions */}
      <div className='flex flex-col gap-2 relative mb-9'>
        {[
          ...runDetails.filter(run => pinnedRuns.has(run.run_id)).sort((a, b) => b.timestamp_utc.localeCompare(a.timestamp_utc)),
          ...runDetails.filter(run => !pinnedRuns.has(run.run_id)).sort((a, b) => b.timestamp_utc.localeCompare(a.timestamp_utc)),
        ].map((run, index, arr) => (
            <RunRow
              run={run}
              isLatest={index === 0 && arr.length > 1}
              tags={run.metadata?.tags}
              totalTasks={run.total_tasks}
              successCount={run.success_count}
              failureCount={run.failure_count}
              timestamp={run.timestamp_utc}
              isSelected={selectedRuns.includes(run.run_id)}
              onToggleExpansion={handleRunClick}
              onToggleSelection={toggleRunSelection}
              onPin={toggleOnPin}
              isPinned={pinnedRuns.has(run.run_id)}
              key={run.run_id}
              index ={index}
            />

        ))}
      </div>

      <StickyCompareBar
        selectedRuns={selectedRuns}
        agentName={agentName}
        onClearSelection={clearSelectedRuns}
        onCompareSelected={compareSelected}
      />

      {/* Add bottom padding to prevent content from being hidden behind the sticky bar */}
    </div>
  );
};

export default AgentRunsView;
