import React from 'react';
import { Button } from '@/components/base/Button';
import cn from 'classnames';

interface RunRowProps {
  runId: string;
  isLatest?: boolean;
  totalTasks: number;
  successCount: number;
  failureCount: number;
  agentName: string;
  timestamp: string;
  isExpanded: boolean;
  isSelected: boolean;
  onToggleExpansion: (runId: string) => void;
  onToggleSelection: (runId: string) => void;
}

function LatestBadge() {
  return (
    <div className="inline-flex items-center px-3 py-1 rounded-full bg-blue-500/10 border border-blue-500/30">
      <span className="text-xs font-semibold text-blue-300">
        Latest
      </span>
    </div>
  );
}

function ChevronIcon({ isExpanded }: { isExpanded: boolean }) {
  return (
    <svg 
      className={cn(
        "h-4 w-4 text-gray-400 transition-transform",
        isExpanded ? "rotate-90" : ""
      )} 
      fill="none" 
      viewBox="0 0 24 24" 
      stroke="currentColor"
    >
      <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 5l7 7-7 7" />
    </svg>
  );
}

const RunRow: React.FC<RunRowProps> = ({
  runId,
  isLatest,
  totalTasks,
  successCount,
  failureCount,
  agentName,
  timestamp,
  isExpanded,
  isSelected,
  onToggleExpansion,
  onToggleSelection,
}) => {
  const successRate = ((successCount / totalTasks) * 100).toFixed(1);

  const handleRowClick = () => {
    onToggleExpansion(runId);
  };

  const handleSelectionClick = (e: React.MouseEvent) => {
    e.stopPropagation();
    onToggleSelection(runId);
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
            <p className="font-noto-sans font-normal leading-5 text-white text-sm truncate" title={runId}>
              {runId}
            </p>
            {isLatest && <LatestBadge />}
          </div>
        </div>
        
        {/* Total Tasks column */}
        <div>
          <p className="font-noto-sans font-normal leading-5 text-white text-sm">
            {totalTasks}
          </p>
        </div>
        
        {/* Success Rate column */}
        <div>
          <p className="font-noto-sans font-normal leading-5 text-sm">
            <span className="text-green-400">{successCount}</span>
            <span className="text-gray-400">/</span>
            <span className="text-red-400">{failureCount}</span>
            <span className="text-gray-400">({successRate}%)</span>
          </p>
        </div>
        
        {/* Agent column */}
        <div>
          <p className="font-noto-sans font-normal leading-5 text-blue-400 text-sm truncate">
            {agentName}
          </p>
        </div>
        
        {/* Timestamp column */}
        <div>
          <p className="font-noto-sans font-normal leading-5 text-gray-300 text-sm" title={timestamp}>
            {new Date(timestamp).toLocaleString()}
          </p>
        </div>

        {/* Compare button column - container prevents layout shift */}
        <div className="w-[130px] flex justify-end">
          <Button
            variant={isSelected ? 'danger' : 'default'}
            onClick={handleSelectionClick}
            className="text-sm whitespace-nowrap"
          >
            {isSelected ? 'Deselect' : 'Add to Compare'}
          </Button>
        </div>
      </div>
    </div>
  );
};

export default RunRow;