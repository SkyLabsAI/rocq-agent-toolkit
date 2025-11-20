import React, { useEffect } from 'react';
import { createPortal } from 'react-dom';
import { Button } from '@/components/base/Button';
import cn from "classnames";

interface StickyCompareBarProps {
  selectedRuns: string[];
  agentName: string;
  onClearSelection: () => void;
  onCompareSelected: () => void;
}

const StickyCompareBar: React.FC<StickyCompareBarProps> = ({
  selectedRuns,
  agentName,
  onClearSelection,
  onCompareSelected,
}) => {
  // Add bottom padding to body when bar is visible to prevent content blocking
  useEffect(() => {
    if (selectedRuns.length > 0 && typeof window !== 'undefined') {
      document.body.style.paddingBottom = '80px';
      return () => {
        document.body.style.paddingBottom = '';
      };
    }
  }, [selectedRuns.length]);

  // Don't render if no runs selected or on server side
  if (selectedRuns.length === 0 || typeof window === 'undefined') {
    return null;
  }

  return createPortal(
    <div className="fixed bottom-0 left-0 right-0 bg-[#222326] backdrop-blur-sm border-t border-[#2B2C2F] z-50 shadow-lg px-10 py-3 flex justify-between items-center">
       <div className=" flex items-center justify-center">
      <div className="flex items-center gap-3.5 w-full max-w-2xl">
        <p className="text-white text-[14px] font-semibold whitespace-nowrap">
          Agent: {agentName}
        </p>
        <div className="w-px h-5 bg-[#F0F1F2]"></div>
        <p className="text-[#E5E9F640] text-[14px] whitespace-nowrap">
          Selected 2 Runs
        </p>
      </div>
    </div>
      
        <div className="flex items-center gap-3">
          <Button
            variant="danger"
            onClick={(e) => { e.stopPropagation(); onClearSelection(); }}
            className="px-4 py-2 text-sm"
          >
            Clear Selection
          </Button>
          <Button
            variant={selectedRuns.length < 2 ? 'ghost' : 'default'}
            disabled={selectedRuns.length < 2}
            onClick={(e) => { e.stopPropagation(); onCompareSelected(); }}
            className={cn(
              "px-6 py-2 text-sm font-medium transition-colors",
             
            )}
          >
            {selectedRuns.length < 2 ? `Select ${2 - selectedRuns.length} more run${2 - selectedRuns.length > 1 ? 's' : ''}` : `Compare ${selectedRuns.length} Runs`}
          </Button>
        </div>

    </div>,
    document.body
  );
};

export default StickyCompareBar;