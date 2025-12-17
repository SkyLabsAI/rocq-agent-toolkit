import React, { useState } from 'react';

import Modal from '@/components/base/ui/modal';

interface TagProps {
  value: string;
  attributeProp: string;
}

const TAG_BACKGROUND_COLOR_CONFIG: Record<string, string> = {
  name: 'bg-chart-categorical-3/15',
  branch: 'bg-chart-categorical-2/15',
};

const TAG_BORDER_COLOR_CONFIG: Record<string, string> = {
  name: 'border-chart-categorical-3/30',
  branch: 'border-chart-categorical-2/30',
};

const TAG_TEXT_COLOR_CONFIG: Record<string, string> = {
  name: 'text-chart-categorical-3',
  branch: 'text-chart-categorical-2',
};

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
      className={`flex items-center px-3 py-1 rounded-full border ${backgroundColor} ${borderColor}`}
      onClick={e => e.stopPropagation()}
    >
      <span
        className={`text-xs font-semibold text-chart-categorical-1 ${textColor}`}
      >
        {value}
      </span>
    </div>
  );
};

interface TagsDisplayProps {
  tags: Record<string, string>;
  maxVisible?: number;
  runId?: string;
}

export const TagsDisplay: React.FC<TagsDisplayProps> = ({
  tags,
  maxVisible = 3,
  runId = '',
}) => {
  const [isModalOpen, setIsModalOpen] = useState(false);

  const tagEntries = Object.entries(tags);
  const visibleTags = tagEntries.slice(0, maxVisible);
  const hiddenCount = tagEntries.length - maxVisible;
  const hasHiddenTags = hiddenCount > 0;

  const handleSeeMoreClick = (e: React.MouseEvent) => {
    e.stopPropagation();
    setIsModalOpen(true);
  };

  const handleModalClose = () => {
    setIsModalOpen(false);
  };

  return (
    <>
      {/* Visible tags */}
      {visibleTags.map(([key, value]) => (
        <Tag value={value} key={key} attributeProp={key} />
      ))}

      {/* See more button */}
      {hasHiddenTags && (
        <button
          onClick={handleSeeMoreClick}
          className='flex items-center px-3 py-1 rounded-full border border-text-disabled/30 bg-elevation-surface-overlay hover:bg-elevation-surface-raised transition-colors'
        >
          <span className='text-xs font-semibold text-text-disabled'>
            +{hiddenCount} more
          </span>
        </button>
      )}

      {/* Tags Modal */}
      <Modal
        isOpen={isModalOpen}
        onClose={handleModalClose}
        title={`All Tags ${runId && `for ${runId}`}`.trim()}
        size='large'
      >
        <div
          className='flex flex-wrap gap-2'
          onClick={e => e.stopPropagation()}
        >
          {tagEntries.map(([key, value]) => (
            <Tag value={value} key={key} attributeProp={key} />
          ))}
        </div>
      </Modal>
    </>
  );
};
