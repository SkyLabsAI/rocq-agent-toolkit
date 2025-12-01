import React, { useEffect } from 'react';
import { createPortal } from 'react-dom';
import { Button } from '@/components/base/Button';

interface StickyCompareBarProps {
  selectedItems: string[];
  // agentName: string;
  onClearSelection: () => void;
  onCompareSelected: () => void;
  attribute: string;
}

const StickyCompareBar: React.FC<StickyCompareBarProps> = ({
  selectedItems,
  // agentName,
  onClearSelection,
  onCompareSelected,
  attribute,
}) => {
  // Add bottom padding to body when bar is visible to prevent content blocking
  useEffect(() => {
    if (selectedItems.length > 0 && typeof window !== 'undefined') {
      document.body.style.paddingBottom = '80px';
      return () => {
        document.body.style.paddingBottom = '';
      };
    }
  }, [selectedItems.length]);

  // Don't render if no runs selected or on server side
  if (selectedItems.length === 0 || typeof window === 'undefined') {
    return null;
  }

  return createPortal(
    <div className="fixed bottom-0 left-0 right-0 bg-elevation-surface-raised backdrop-blur-sm border-t border-t-elevation-surface-overlay  z-50 shadow-lg px-10 py-3 flex justify-between items-center">
       <div className=" flex items-center justify-center">
      <div className="flex items-center gap-3.5 w-full max-w-2xl h-[42px]">
        {/* <p className="text-text text-[14px] font-semibold whitespace-nowrap">
          Agent: {agentName}
        </p> */}
        <div className="w-px h-5 bg-text"></div>
        <p className="text-text-disabled text-[14px] whitespace-nowrap">
          Selected {selectedItems.length} {attribute}
        </p>
      </div>
    </div>
      
        <div className="flex items-center gap-3">
          <Button
            variant="danger"
            onClick={(e) => { e.stopPropagation(); onClearSelection(); }}
    
          >
            Clear Selection
          </Button>
          <Button
            variant="default"
            disabled={selectedItems.length < 2}
            onClick={(e) => { e.stopPropagation(); onCompareSelected(); }}
            
          >
            {selectedItems.length < 2 ? 'Select 1 more run' : `Compare ${selectedItems.length} ${attribute}`}
          </Button>
        </div>

    </div>,
    document.body
  );
};

export default StickyCompareBar;