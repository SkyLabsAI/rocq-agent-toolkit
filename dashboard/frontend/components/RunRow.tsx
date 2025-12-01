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

// Chart color config
const TAG_BACKGROUND_COLOR_CONFIG: Record<string, string> = {
  "name": 'bg-chart-categorical-3/15',
  "branch": 'bg-chart-categorical-2/15',
}

const TAG_BORDER_COLOR_CONFIG: Record<string, string> = {
  "name": 'border-chart-categorical-3/30',
  "branch": 'border-chart-categorical-2/30',
}

const TAG_TEXT_COLOR_CONFIG: Record<string, string> = {
  "name": 'text-chart-categorical-3',
  "branch": 'text-chart-categorical-2',
}

const BG_CHART_COLORS = [
  'bg-chart-categorical-1/15',
  'bg-chart-categorical-2/15',
  'bg-chart-categorical-3/15',
  'bg-chart-categorical-4/15',
  'bg-chart-categorical-5/15',
  'bg-chart-categorical-6/15',
  'bg-chart-categorical-7/15',
  'bg-chart-categorical-8/15',
  'bg-chart-categorical-9/15',
  'bg-chart-categorical-10/15',
];

const BORDER_CHART_COLORS = [
  'border-chart-categorical-1/30',
  'border-chart-categorical-2/30',
  'border-chart-categorical-3/30',
  'border-chart-categorical-4/30',
  'border-chart-categorical-5/30',
  'border-chart-categorical-6/30',
  'border-chart-categorical-7/30',
  'border-chart-categorical-8/30',
  'border-chart-categorical-9/30',
  'border-chart-categorical-10/30',
];

const TEXT_CHART_COLORS = [
  'text-chart-categorical-1',
  'text-chart-categorical-2',
  'text-chart-categorical-3',
  'text-chart-categorical-4',
  'text-chart-categorical-5',
  'text-chart-categorical-6',
  'text-chart-categorical-7',
  'text-chart-categorical-8',
  'text-chart-categorical-9',
  'text-chart-categorical-10',
];

interface TagProps {
  value: string;
  attributeProp: string;
}

const Tag: React.FC<TagProps> = ({ value, attributeProp }) => {
  // Try config first
  let backgroundColor = TAG_BACKGROUND_COLOR_CONFIG[attributeProp];
  let borderColor = TAG_BORDER_COLOR_CONFIG[attributeProp];
  let textColor = TAG_TEXT_COLOR_CONFIG[attributeProp];
  
  // If not found, pick a color based on hash of attributeProp for consistency
  if (!backgroundColor) {
    let hash = 0;
    for (let i = 0; i < attributeProp.length; i++) {
      hash = attributeProp.charCodeAt(i) + ((hash << 5) - hash);
    }
    const idx = Math.abs(hash) % BG_CHART_COLORS.length;
     backgroundColor = BG_CHART_COLORS[idx];
     borderColor = BORDER_CHART_COLORS[idx];
     textColor = TEXT_CHART_COLORS[idx];
  }
  return (
    <div
      className={`flex items-center  px-3 py-1 rounded-full border ${backgroundColor} ${borderColor}`}
    >
      <span className={`text-xs font-semibold text-chart-categorical-1  ${textColor}`}>
        {value}
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
  isPinned = false,
  onPin,
  index,
  tags
}) => {


  const successRate = ((successCount / totalTasks) * 100).toFixed(1);

  const handleRowClick = () => {
    onToggleExpansion(run);
  };

  const handleSelectionClick = (e: React.MouseEvent) => {
    e.stopPropagation();
    onToggleSelection(run);
  };

  return ( <div className="grid grid-cols-[5fr_1fr_1fr_1fr_1.2fr_auto] gap-4 items-center p-2.5 hover:bg-white/10 transition-colors cursor-pointer rounded-lg overflow-hidden bg-elevation-surface-raised" style={{top: 78 * index + 0}} onClick={handleRowClick}>
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
                <Tag value={value} key={key} attributeProp={key}/>
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