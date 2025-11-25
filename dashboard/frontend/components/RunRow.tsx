import React from 'react';
import { Button } from '@/components/base/Button';
import cn from 'classnames';
import { Run } from '@/contexts/SelectedRunContext';
import { PinOutlineIcon } from '@/icons/pin-outline';
import { PinIcon } from '@/icons/pin';

interface RunRowProps {
  run: Run;
  isLatest?: boolean;
  totalTasks: number;
  successCount: number;
  failureCount: number;
  timestamp: string;
  isSelected: boolean;
  isPinned: boolean;
  index: number
  onToggleExpansion: (runId: Run) => void;
  onToggleSelection: (runId: Run) => void;
  onPin: (runId: Run) => void;
  tags?: Record<string, string>;
}

function LatestBadge() {
  return (
    <div className="flex items-center px-3 py-1 rounded-full bg-background-information border border-blue-500/30">
      <span className="text-xs font-semibold text-text-information">
        Latest
      </span>
    </div>
  );
}

const Tag: React.FC<{ value: string }> = ({ value }) => {
  return <div className="flex items-center px-3 py-1 rounded-full bg-background-information border border-blue-500/30">
      <span className="text-xs font-semibold text-text-information">
        {value}
      </span>
    </div>
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
  isPinned = false,
  onPin,
  index,
  tags
}) => {

  console.log("Rendering RunRow for run:", run.run_id);
  console.log(tags)

  const successRate = ((successCount / totalTasks) * 100).toFixed(1);

  const handleRowClick = () => {
    onToggleExpansion(run);
  };

  const handleSelectionClick = (e: React.MouseEvent) => {
    e.stopPropagation();
    onToggleSelection(run);
  };

  return ( <div className="grid grid-cols-[5fr_1fr_1fr_1fr_1.2fr_auto] gap-4 items-center p-2.5 hover:bg-white/10 transition-colors cursor-pointer rounded-lg overflow-hidden rounded-lg bg-elevation-surface-raised" style={{top: 78 * index + 0}} onClick={handleRowClick}>
        {/* Run ID column with chevron */}
        <div className="flex gap-2 items-center min-w-0">

          <div className="flex items-center gap-2 min-w-0">
            <button title='pin' className='flex items-center' onClick={e=>{e.stopPropagation();onPin(run)}}>
             {isPinned? <PinIcon className='text-text-selected'/>: <PinOutlineIcon className='opacity-0 hover:opacity-100'/>}

            </button>
            <p className="font-noto-sans font-normal text-[14px] leading-5 text-text text-sm truncate" title={run.run_id}>
              {run.run_id}
            </p>
            {isLatest && <LatestBadge />}
            {tags && Object.entries(tags).map(([key, value])=>(           
                <Tag value={value} key={key}/>
            ))}
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
   
  );
};

export default RunRow;