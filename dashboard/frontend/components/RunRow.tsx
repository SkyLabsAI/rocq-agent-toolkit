import React from 'react';
import { Button } from '@/components/base/Button';
import cn from 'classnames';
import { Run } from '@/contexts/SelectedRunContext';
import { TaskOutput } from '@/types/types';

interface RunRowProps {
  run: Run;
  isLatest?: boolean;
  totalTasks: number;
  successCount: number;
  failureCount: number;
  timestamp: string;
  isSelected: boolean;
  onToggleExpansion: (runId: Run) => void;
  onToggleSelection: (runId: Run) => void;
}

function LatestBadge() {
  return (
    <div className="inline-flex items-center px-3 py-1 rounded-full bg-background-information border border-blue-500/30">
      <span className="text-xs font-semibold text-text-information">
        Latest
      </span>
    </div>
  );
}



const  RunRow: React.FC<RunRowProps> = ({
  run,
  isLatest,
  totalTasks,
  successCount,
  failureCount,
  timestamp,
  isSelected,
  onToggleExpansion,
  onToggleSelection,

}) => {
  const successRate = ((successCount / totalTasks) * 100).toFixed(1);

  const handleRowClick = () => {
    onToggleExpansion(run);
  };

  const handleSelectionClick = (e: React.MouseEvent) => {
    e.stopPropagation();
    onToggleSelection(run);
  };

  return (
    <div 
      className="bg-white/5 hover:bg-white/10 transition-colors cursor-pointer"
      onClick={handleRowClick}
    >
      {/* Using CSS Grid with fractional units to match header layout exactly */}
      <div className="grid grid-cols-[2fr_1fr_1fr_1fr_1.2fr_auto] gap-4 items-center p-4">
        {/* Run ID column with chevron */}
        <div className="flex gap-2 items-center min-w-0">

          <div className="flex items-center gap-2 min-w-0">
            <p className="font-noto-sans font-normal text-[14px] leading-5 text-text text-sm truncate" title={run.run_id}>
              {run.run_id}
            </p>
            {isLatest && <LatestBadge />}
          </div>
        </div>
        
        {/* Total Tasks column */}
        <div>
          <p className="font-noto-sans font-normal leading-5 text-text text-sm">
            {totalTasks}
          </p>
        </div>
        
        {/* Success Rate column */}
        <div>
          <p className="font-noto-sans font-normal leading-5 text-sm">
            <span className="text-text-success">{successCount}</span>
            <span className="text-text-disabled">/</span>
            <span className="text-text-danger">{failureCount}</span>
            <span className="text-text-disabled">{`  (${successRate}%)`}</span>
          </p>
        </div>
        
      
        
        {/* Timestamp column */}
        <div>
          <p className="font-noto-sans font-normal leading-5 text-text text-sm" title={timestamp}>
            {new Date(timestamp).toLocaleString()}
          </p>
        </div>

        {/* Compare button column - container prevents layout shift */}
        <div className="flex-1 flex justify-end">
          <Button
            variant={isSelected ? 'danger' : 'default'}
            onClick={handleSelectionClick}
            className="text-sm whitespace-nowrap text-[14px] font-normal"
          >
            {isSelected ? 'Deselect' : 'Add to Compare'}
          </Button>
        </div>
      </div>
    </div>
  );
};

export default RunRow;