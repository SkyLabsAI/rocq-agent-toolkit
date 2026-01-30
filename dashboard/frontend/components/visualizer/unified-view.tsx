'use client';

import React, { useMemo, useState } from 'react';

import FlamegraphView from '@/components/visualizer/flamegraph-view';
import SpanGraphView from '@/components/visualizer/span-graph-view';
import type { EnhancedSpan } from '@/services/visualizer/process-tree';
import type { VisualizerSpanLite } from '@/services/visualizer';

type Props = {
  spans: VisualizerSpanLite[];
  enhancedSpans: EnhancedSpan[];
  selectedSpanId?: string;
  onSelectSpanId: (spanId: string) => void;
  successPathNodes: Set<string>;
  collapsedNodes: Set<string>;
  onToggleCollapse: (spanId: string) => void;
  isRightPanelOpen?: boolean;
  onToggleRightPanel?: () => void;
};

const UnifiedView = ({
  spans,
  enhancedSpans,
  selectedSpanId,
  onSelectSpanId,
  successPathNodes,
  collapsedNodes,
  onToggleCollapse,
  isRightPanelOpen,
  onToggleRightPanel,
}: Props) => {
  const [viewMode, setViewMode] = useState<'split' | 'traces' | 'flamegraph'>(
    'split'
  );

  return (
    <div className='flex flex-col h-full gap-3'>
      {/* View Mode Toggle */}
      <div className='flex items-center justify-between gap-2 bg-elevation-surface-raised p-2 rounded-lg border border-elevation-surface-overlay'>
        <div className='flex items-center gap-2'>
          <div className='text-sm text-text font-semibold'>View:</div>
          <div className='flex gap-1'>
            <button
              onClick={() => setViewMode('split')}
              className={`px-3 py-1.5 text-sm rounded border transition-colors ${
                viewMode === 'split'
                  ? 'bg-background-brand-bold text-white border-background-brand-bold font-medium'
                  : 'bg-elevation-surface-sunken text-text border-elevation-surface-overlay hover:bg-elevation-surface-overlay hover:border-border-bold'
              }`}
            >
              Split View
            </button>
            <button
              onClick={() => setViewMode('traces')}
              className={`px-3 py-1.5 text-sm rounded border transition-colors ${
                viewMode === 'traces'
                  ? 'bg-background-brand-bold text-white border-background-brand-bold font-medium'
                  : 'bg-elevation-surface-sunken text-text border-elevation-surface-overlay hover:bg-elevation-surface-overlay hover:border-border-bold'
              }`}
            >
              Traces Only
            </button>
            <button
              onClick={() => setViewMode('flamegraph')}
              className={`px-3 py-1.5 text-sm rounded border transition-colors ${
                viewMode === 'flamegraph'
                  ? 'bg-background-brand-bold text-white border-background-brand-bold font-medium'
                  : 'bg-elevation-surface-sunken text-text border-elevation-surface-overlay hover:bg-elevation-surface-overlay hover:border-border-bold'
              }`}
            >
              Flamegraph Only
            </button>
          </div>
        </div>
        {onToggleRightPanel && (
          <button
            onClick={onToggleRightPanel}
            className='px-3 py-2 bg-elevation-surface-sunken hover:bg-elevation-surface-overlay rounded-lg border border-elevation-surface-overlay text-text text-sm font-medium transition-colors shadow-sm'
            title={isRightPanelOpen ? 'Close panel' : 'Open panel'}
          >
            {isRightPanelOpen ? '→' : '←'} Info
          </button>
        )}
      </div>

      {/* Visualization Area */}
      <div className='flex-1 min-h-0'>
        {viewMode === 'split' ? (
          <div className='flex flex-col h-full gap-3'>
            {/* Traces Graph - Top */}
            <div className='flex-1 min-h-0'>
              <SpanGraphView
                spans={enhancedSpans}
                selectedSpanId={selectedSpanId}
                onSelectSpanId={onSelectSpanId}
                successPathNodes={successPathNodes}
                collapsedNodes={collapsedNodes}
                onToggleCollapse={onToggleCollapse}
              />
            </div>

            {/* Flamegraph - Bottom */}
            <div className='flex-1 min-h-0'>
              <FlamegraphView
                spans={spans}
                selectedSpanId={selectedSpanId}
                onSelectSpanId={onSelectSpanId}
                isRightPanelOpen={isRightPanelOpen}
                onToggleRightPanel={onToggleRightPanel}
              />
            </div>
          </div>
        ) : viewMode === 'traces' ? (
          <SpanGraphView
            spans={enhancedSpans}
            selectedSpanId={selectedSpanId}
            onSelectSpanId={onSelectSpanId}
            successPathNodes={successPathNodes}
            collapsedNodes={collapsedNodes}
            onToggleCollapse={onToggleCollapse}
          />
        ) : (
          <FlamegraphView
            spans={spans}
            selectedSpanId={selectedSpanId}
            onSelectSpanId={onSelectSpanId}
            isRightPanelOpen={isRightPanelOpen}
            onToggleRightPanel={onToggleRightPanel}
          />
        )}
      </div>
    </div>
  );
};

export default UnifiedView;
