import React, { useState } from 'react';
import TaskButton from "@/components/base/taskButton";
import { Button } from '@/components/base/Button';
import RunRow from '@/components/RunRow';
import RunDetailsView from '@/components/RunDetailsView';
import StickyCompareBar from '@/components/StickyCompareBar';
import cn from "classnames";

interface AgentRunsViewProps {
  runDetails: any[];
  agentName: string;
  selectedRuns: string[];
  loadingLogs: string | null;
  toggleRunSelection: (runId: string) => void;
  clearSelectedRuns: () => void;
  compareSelected: () => void;
  openCodeModal: (task: any) => void;
}

const AgentRunsView: React.FC<AgentRunsViewProps> = ({
  runDetails,
  agentName,
  selectedRuns,
  loadingLogs,
  toggleRunSelection,
  clearSelectedRuns,
  compareSelected,
  openCodeModal,
}) => {
  const [selectedRunId, setSelectedRunId] = useState<string | null>(null);

  const handleRunClick = (runId: string) => {
    setSelectedRunId(runId);
  };

  const handleBackToRuns = () => {
    setSelectedRunId(null);
  };

  // If a run is selected, show the full-screen view
  if (selectedRunId) {
    const selectedRun = runDetails.find(run => run.run_id === selectedRunId);
    
    if (selectedRun) {
      return (
        <RunDetailsView
          run={selectedRun}
          loadingLogs={loadingLogs}
          onBack={handleBackToRuns}
          openCodeModal={openCodeModal}
        />
      );
    }
  }
  return (
    <div className="space-y-4">
      {/* Header using CSS Grid with fractional units for perfect alignment */}
      <div className="grid grid-cols-[2fr_1fr_1fr_1fr_1.2fr_auto] gap-4 items-center mb-4 p-4">
        <div className="flex gap-2 items-center">
          <p className="font-noto-sans font-normal leading-5 text-gray-400 text-sm">Run ID</p>
        </div>
        
        <div>
          <p className="font-noto-sans font-normal leading-5 text-gray-400 text-sm">Total Tasks</p>
        </div>
        
        <div>
          <p className="font-noto-sans font-normal leading-5 text-gray-400 text-sm">Success Rate</p>
        </div>
        
        <div>
          <p className="font-noto-sans font-normal leading-5 text-gray-400 text-sm">Agent</p>
        </div>
        
        <div>
          <p className="font-noto-sans font-normal leading-5 text-gray-400 text-sm">Timestamp</p>
        </div>
        
        <div>
          {/* Invisible button to match content row button dimensions */}
          <div className="bg-transparent relative rounded border border-transparent opacity-0 pointer-events-none">
            <div className="flex gap-1.5 items-center px-3 py-2 relative rounded-inherit">
              <p className="font-noto-sans font-normal leading-5 text-transparent text-sm whitespace-nowrap">
                Add to Compare
              </p>
            </div>
          </div>
        </div>
      </div>
      
      {/* Admin view: Runs list with selectable compare actions */}
      <div className="flex flex-col gap-2">
      {runDetails.map((run, index) => (
        <div key={run.run_id} className="border border-white/10 rounded-lg overflow-hidden">
          <RunRow
            runId={run.run_id}
            isLatest={index === 0 && runDetails.length > 1}
            totalTasks={run.total_tasks}
            successCount={run.success_count}
            failureCount={run.failure_count}
            agentName={run.agent_name}
            timestamp={run.timestamp_utc}
            isExpanded={false}
            isSelected={selectedRuns.includes(run.run_id)}
            onToggleExpansion={handleRunClick}
            onToggleSelection={toggleRunSelection}
          />
        </div>
      ))}
      </div>
      
      {/* Add bottom padding to prevent content from being hidden behind the sticky bar */}
      {selectedRuns.length > 0 && <div className="h-20"></div>}
      
      {/* Sticky bottom compare bar component */}
      <StickyCompareBar
        selectedRuns={selectedRuns}
        agentName={agentName}
        onClearSelection={clearSelectedRuns}
        onCompareSelected={compareSelected}
      />
    </div>
  );
};

export default AgentRunsView;