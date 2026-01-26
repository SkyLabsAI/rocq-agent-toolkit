'use client';

import { useMemo, useState } from 'react';

import type { VisualizerSpanLite } from '@/services/visualizer';

type Props = {
  spans: VisualizerSpanLite[];
  selectedSpanId?: string;
  onSelectSpanId: (spanId: string) => void;
};

const FlamegraphView = ({ spans, selectedSpanId, onSelectSpanId }: Props) => {
  const [hoveredSpanId, setHoveredSpanId] = useState<string | null>(null);
  const [tooltipPosition, setTooltipPosition] = useState<{
    x: number;
    y: number;
  } | null>(null);

  const flamegraphData = useMemo(() => {
    if (!spans.length) return null;

    // Build parent-child relationships - use raw span data
    const childrenMap = new Map<string, string[]>();
    const spanMap = new Map<string, VisualizerSpanLite>();

    for (const span of spans) {
      spanMap.set(span.span_id, span);
      const parentId = span.parent_span_id;
      if (parentId) {
        if (!childrenMap.has(parentId)) {
          childrenMap.set(parentId, []);
        }
        childrenMap.get(parentId)!.push(span.span_id);
      }
    }

    // Find root spans (no parent or parent not in the set)
    const rootSpans = spans.filter(
      s => !s.parent_span_id || !spanMap.has(s.parent_span_id)
    );

    // Calculate position and width for each span
    const layoutMap = new Map<
      string,
      {
        leftPercent: number;
        widthPercent: number;
        depth: number;
      }
    >();

    // Process spans recursively starting from roots
    const processSpan = (
      spanId: string,
      leftPercent: number,
      widthPercent: number,
      depth: number
    ) => {
      layoutMap.set(spanId, { leftPercent, widthPercent, depth });

      const children = childrenMap.get(spanId) || [];
      if (children.length === 0) return;

      // Divide width equally among children
      const childWidth = widthPercent / children.length;

      children.forEach((childId, index) => {
        const childLeft = leftPercent + index * childWidth;
        processSpan(childId, childLeft, childWidth, depth + 1);
      });
    };

    // Start with root spans dividing the full width
    const rootWidth = 100 / rootSpans.length;
    rootSpans.forEach((root, index) => {
      processSpan(root.span_id, index * rootWidth, rootWidth, 0);
    });

    const maxDepth = Math.max(
      ...Array.from(layoutMap.values()).map(l => l.depth),
      0
    );

    // Create layout data for each span
    const layoutSpans = spans
      .filter(span => layoutMap.has(span.span_id))
      .map(span => {
        const layout = layoutMap.get(span.span_id)!;

        // Determine color based on depth (flame gradient)
        // Deeper spans = cooler colors, shallower = hotter colors
        let colorClass = '';

        if (layout.depth === 0) {
          // Root - hottest red
          colorClass = 'bg-red-600 hover:bg-red-700';
        } else if (layout.depth === 1) {
          // First level - orange-red
          colorClass = 'bg-orange-600 hover:bg-orange-700';
        } else if (layout.depth === 2) {
          // Second level - orange
          colorClass = 'bg-orange-500 hover:bg-orange-600';
        } else if (layout.depth === 3) {
          // Third level - amber
          colorClass = 'bg-amber-500 hover:bg-amber-600';
        } else if (layout.depth === 4) {
          // Fourth level - yellow
          colorClass = 'bg-yellow-500 hover:bg-yellow-600';
        } else {
          // Deeper - light yellow
          colorClass = 'bg-yellow-400 hover:bg-yellow-500';
        }

        return {
          span,
          leftPercent: layout.leftPercent,
          widthPercent: layout.widthPercent,
          depth: layout.depth,
          colorClass,
        };
      });

    return {
      spans: layoutSpans,
      maxDepth,
    };
  }, [spans]);

  if (!spans.length) {
    return (
      <div className='text-sm text-text-disabled'>No spans to render.</div>
    );
  }

  if (!flamegraphData) {
    return (
      <div className='text-sm text-text-danger'>
        Unable to render flamegraph - no valid span data.
      </div>
    );
  }

  const rowHeight = 32;
  const rowGap = 4;
  const totalHeight = (flamegraphData.maxDepth + 1) * (rowHeight + rowGap);

  const formatPercent = (value: number): string => {
    return `${value.toFixed(2)}%`;
  };

  const hoveredSpan = hoveredSpanId
    ? flamegraphData.spans.find(s => s.span.span_id === hoveredSpanId)
    : null;

  return (
    <div className='w-full h-full flex flex-col rounded-lg border border-elevation-surface-overlay overflow-hidden bg-elevation-surface-sunken'>
      {/* Header with info */}
      <div className='bg-elevation-surface-raised border-b border-elevation-surface-overlay p-3'>
        <div className='flex justify-between items-center text-xs text-text-disabled'>
          <div>Spans: {spans.length}</div>
          {hoveredSpan && (
            <div className='text-text font-medium'>
              <span className='font-semibold'>{hoveredSpan.span.name}</span>
              <span className='mx-2'>•</span>
              <span className='text-orange-500'>
                Depth: {hoveredSpan.depth}
              </span>
              <span className='mx-2'>•</span>
              <span className='text-text-disabled'>
                {formatPercent(hoveredSpan.widthPercent)} width
              </span>
            </div>
          )}
        </div>
      </div>

      {/* Hover Tooltip */}
      {hoveredSpan && tooltipPosition && (
        <div
          className='fixed z-50 pointer-events-none'
          style={{
            left: `${tooltipPosition.x}px`,
            top: `${tooltipPosition.y}px`,
            transform: 'translate(-50%, -100%)',
          }}
        >
          <div className='bg-gray-900 text-white rounded-lg shadow-xl border border-gray-700 p-3 max-w-xs'>
            <div className='space-y-2'>
              <div className='font-semibold text-sm border-b border-gray-700 pb-2'>
                {hoveredSpan.span.name}
              </div>
              <div className='grid grid-cols-2 gap-x-4 gap-y-1 text-xs'>
                <div className='text-gray-400'>Depth:</div>
                <div className='text-orange-400 font-medium'>
                  Level {hoveredSpan.depth}
                </div>

                <div className='text-gray-400'>Width:</div>
                <div className='text-yellow-400 font-medium'>
                  {formatPercent(hoveredSpan.widthPercent)}
                </div>

                <div className='text-gray-400'>Service:</div>
                <div className='text-white truncate'>
                  {hoveredSpan.span.service_name}
                </div>

                <div className='text-gray-400'>Span ID:</div>
                <div className='text-gray-300 font-mono text-[10px]'>
                  {hoveredSpan.span.span_id.slice(0, 16)}...
                </div>
              </div>

              {/* Additional attributes */}
              {hoveredSpan.span.attributes &&
                Object.keys(hoveredSpan.span.attributes).length > 0 && (
                  <div className='pt-2 border-t border-gray-700'>
                    <div className='text-gray-400 text-xs mb-1'>
                      Attributes:
                    </div>
                    <div className='text-[10px] space-y-1 max-h-20 overflow-y-auto'>
                      {Object.entries(hoveredSpan.span.attributes)
                        .slice(0, 5)
                        .map(([key, value]) => (
                          <div key={key} className='flex gap-2'>
                            <span className='text-blue-400'>{key}:</span>
                            <span className='text-gray-300 truncate'>
                              {String(value)}
                            </span>
                          </div>
                        ))}
                    </div>
                  </div>
                )}
            </div>

            {/* Triangle pointer */}
            <div
              className='absolute left-1/2 bottom-0 transform -translate-x-1/2 translate-y-full'
              style={{
                width: 0,
                height: 0,
                borderLeft: '6px solid transparent',
                borderRight: '6px solid transparent',
                borderTop: '6px solid #1f2937',
              }}
            />
          </div>
        </div>
      )}

      {/* Flamegraph canvas */}
      <div className='flex-1 overflow-auto p-4'>
        <div
          className='relative w-full'
          style={{ height: `${totalHeight}px`, minHeight: '200px' }}
        >
          {flamegraphData.spans.map(layoutSpan => {
            const isSelected = layoutSpan.span.span_id === selectedSpanId;
            const isHovered = layoutSpan.span.span_id === hoveredSpanId;

            // Skip spans that are too narrow to see
            if (layoutSpan.widthPercent < 0.1) return null;

            const top = layoutSpan.depth * (rowHeight + rowGap);

            return (
              <button
                key={layoutSpan.span.span_id}
                type='button'
                onClick={() => onSelectSpanId(layoutSpan.span.span_id)}
                onMouseEnter={e => {
                  setHoveredSpanId(layoutSpan.span.span_id);
                  const rect = e.currentTarget.getBoundingClientRect();
                  setTooltipPosition({
                    x: rect.left + rect.width / 2,
                    y: rect.top - 10,
                  });
                }}
                onMouseLeave={() => {
                  setHoveredSpanId(null);
                  setTooltipPosition(null);
                }}
                className={`absolute rounded border transition-all cursor-pointer ${
                  layoutSpan.colorClass
                } ${
                  isSelected
                    ? 'ring-2 ring-primary-default border-white z-20 shadow-lg'
                    : isHovered
                      ? 'border-white z-10 shadow-md scale-105'
                      : 'border-black/20 hover:shadow-md'
                }`}
                style={{
                  left: `${layoutSpan.leftPercent}%`,
                  width: `${layoutSpan.widthPercent}%`,
                  top: `${top}px`,
                  height: `${rowHeight}px`,
                  minWidth: '2px',
                }}
              >
                {/* Show text only if there's enough space */}
                {layoutSpan.widthPercent > 3 && (
                  <div className='px-2 flex items-center h-full overflow-hidden'>
                    <span className='text-xs font-medium truncate text-white drop-shadow'>
                      {layoutSpan.span.name}
                    </span>
                  </div>
                )}
              </button>
            );
          })}
        </div>
      </div>

      {/* Legend */}
      <div className='bg-elevation-surface-raised border-t border-elevation-surface-overlay p-3'>
        <div className='flex gap-4 text-xs items-center'>
          <span className='text-text-disabled font-medium'>
            Flame Gradient (by depth):
          </span>
          <div className='flex items-center gap-2'>
            <div className='w-4 h-4 rounded bg-red-600 border border-gray-700' />
            <span className='text-text-disabled'>Root (depth 0)</span>
          </div>
          <div className='flex items-center gap-2'>
            <div className='w-4 h-4 rounded bg-orange-500 border border-gray-700' />
            <span className='text-text-disabled'>Shallow (1-2)</span>
          </div>
          <div className='flex items-center gap-2'>
            <div className='w-4 h-4 rounded bg-yellow-500 border border-gray-700' />
            <span className='text-text-disabled'>Medium (3-4)</span>
          </div>
          <div className='flex items-center gap-2'>
            <div className='w-4 h-4 rounded bg-yellow-400 border border-gray-700' />
            <span className='text-text-disabled'>Deep (5+)</span>
          </div>
        </div>
      </div>
    </div>
  );
};

export default FlamegraphView;
