'use client';

import React, { useMemo, useState } from 'react';

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
    showLeft: boolean;
    showAbove: boolean;
  } | null>(null);
  const containerRef = React.useRef<HTMLDivElement>(null);

  // Zoom state: represents the visible portion of the timeline (0-100%)
  const [zoomStart, setZoomStart] = useState(0);
  const [zoomEnd, setZoomEnd] = useState(100);

  const flamegraphData = useMemo(() => {
    if (!spans.length) return null;

    // Build parent-child relationships
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

    // Calculate depth for each span via recursion
    const depthMap = new Map<string, number>();

    const calculateDepth = (spanId: string, depth: number) => {
      depthMap.set(spanId, depth);
      const children = childrenMap.get(spanId) || [];
      children.forEach(childId => calculateDepth(childId, depth + 1));
    };

    rootSpans.forEach(root => calculateDepth(root.span_id, 0));

    // Calculate position and width using equal distribution for children
    const layoutMap = new Map<
      string,
      {
        leftPercent: number;
        widthPercent: number;
        depth: number;
      }
    >();

    // Recursive function to calculate layout with equal width distribution
    const calculateLayout = (
      spanId: string,
      parentLeft: number,
      parentWidth: number
    ) => {
      const depth = depthMap.get(spanId) ?? 0;
      const children = childrenMap.get(spanId) || [];

      // Set layout for current span
      layoutMap.set(spanId, {
        leftPercent: parentLeft,
        widthPercent: parentWidth,
        depth,
      });

      // If this span has children, divide its width equally among them
      if (children.length > 0) {
        const childWidth = parentWidth / children.length;
        children.forEach((childId, index) => {
          const childLeft = parentLeft + index * childWidth;
          calculateLayout(childId, childLeft, childWidth);
        });
      }
    };

    // Start with root spans, each taking equal portion of 100%
    const rootWidth = 100 / rootSpans.length;
    rootSpans.forEach((root, index) => {
      const rootLeft = index * rootWidth;
      calculateLayout(root.span_id, rootLeft, rootWidth);
    });

    const maxDepth = Math.max(...Array.from(depthMap.values()), 0);

    // Create layout data for each span
    const layoutSpans = spans.map(span => {
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

  // Calculate zoom scale - how much the canvas should expand
  const zoomRange = zoomEnd - zoomStart;
  const zoomScale = 100 / zoomRange; // e.g., if viewing 10%, scale = 10x

  // Transform position/width for expanded canvas
  const transformToZoom = (leftPercent: number, widthPercent: number) => {
    const spanEnd = leftPercent + widthPercent;

    // Check if span is visible in zoom range
    if (spanEnd < zoomStart || leftPercent > zoomEnd) {
      return null; // Span is outside zoom range
    }

    // Position within the expanded canvas
    // Shift everything left by zoomStart, then scale positions
    const newLeft = (leftPercent - zoomStart) * zoomScale;
    const newWidth = widthPercent * zoomScale;

    return {
      leftPercent: newLeft,
      widthPercent: newWidth,
    };
  };

  const resetZoom = () => {
    setZoomStart(0);
    setZoomEnd(100);
  };

  const isZoomed = zoomStart !== 0 || zoomEnd !== 100;

  const hoveredSpan = hoveredSpanId
    ? flamegraphData.spans.find(s => s.span.span_id === hoveredSpanId)
    : null;

  return (
    <div
      ref={containerRef}
      className='w-full h-full flex flex-col rounded-lg border border-elevation-surface-overlay overflow-hidden bg-elevation-surface-sunken'
    >
      {/* Header with info */}
      <div className='bg-elevation-surface-raised border-b border-elevation-surface-overlay p-3'>
        <div className='flex justify-between items-center text-xs text-text-disabled'>
          <div className='flex gap-4 items-center'>
            <span>Spans: {spans.length}</span>
            <span className='text-text-subtlest'>•</span>
            <span className='text-text-disabled text-[10px] font-mono'>
              Zoom: {zoomStart.toFixed(1)}% - {zoomEnd.toFixed(1)}%
            </span>
            {isZoomed && (
              <button
                onClick={resetZoom}
                className='px-3 py-1 bg-primary-default hover:bg-primary-hovered text-white rounded text-xs font-medium transition-colors shadow-sm'
                title='Reset to full timeline view'
              >
                Reset View
              </button>
            )}
          </div>
          {hoveredSpan && (
            <div className='text-text font-medium'>
              <span className='font-semibold'>{hoveredSpan.span.name}</span>
              <span className='mx-2'>•</span>
              <span className='text-orange-500'>
                Depth: {hoveredSpan.depth}
              </span>
              <span className='mx-2'>•</span>
              <span className='text-text-disabled'>
                {formatPercent(hoveredSpan.widthPercent)} of view
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
            transform: `translate(${tooltipPosition.showLeft ? '-100%' : '0'}, ${tooltipPosition.showAbove ? '-100%' : '0'})`,
            marginLeft: tooltipPosition.showLeft ? '-10px' : '10px',
            marginTop: tooltipPosition.showAbove ? '-10px' : '10px',
          }}
        >
          <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg shadow-xl p-4 min-w-[400px] max-w-2xl backdrop-blur-sm'>
            <div className='space-y-3'>
              <div className='font-semibold text-sm text-text border-b border-elevation-surface-overlay pb-2'>
                {hoveredSpan.span.name}
              </div>
              <div className='grid grid-cols-[auto_1fr] gap-x-6 gap-y-2 text-xs'>
                <div className='text-text-disabled'>Depth:</div>
                <div className='text-orange-500 font-medium'>
                  Level {hoveredSpan.depth}
                </div>

                <div className='text-text-disabled'>% of View:</div>
                <div className='text-yellow-500 font-medium'>
                  {formatPercent(hoveredSpan.widthPercent)}
                </div>

                <div className='text-text-disabled'>Service:</div>
                <div className='text-text font-medium'>
                  {hoveredSpan.span.service_name}
                </div>

                <div className='text-text-disabled'>Span ID:</div>
                <div className='text-text font-mono text-[11px] break-all'>
                  {hoveredSpan.span.span_id}
                </div>

                {hoveredSpan.span.parent_span_id && (
                  <>
                    <div className='text-text-disabled'>Parent Span:</div>
                    <div className='text-text-subtlest font-mono text-[11px] break-all'>
                      {hoveredSpan.span.parent_span_id}
                    </div>
                  </>
                )}
              </div>

              {/* Additional attributes */}
              {hoveredSpan.span.attributes &&
                Object.keys(hoveredSpan.span.attributes).length > 0 && (
                  <div className='pt-2 border-t border-elevation-surface-overlay'>
                    <div className='text-text-disabled text-xs font-medium mb-2'>
                      Attributes:
                    </div>
                    <div className='text-[11px] space-y-1.5 max-h-32 overflow-y-auto'>
                      {Object.entries(hoveredSpan.span.attributes).map(
                        ([key, value]) => (
                          <div key={key} className='flex gap-3'>
                            <span className='text-text-disabled font-medium min-w-[120px]'>
                              {key}:
                            </span>
                            <span className='text-text break-all'>
                              {String(value)}
                            </span>
                          </div>
                        )
                      )}
                    </div>
                  </div>
                )}
            </div>
          </div>
        </div>
      )}

      {/* Flamegraph canvas */}
      <div className='flex-1 overflow-auto p-4 overscroll-x-contain'>
        <div
          className='relative select-none'
          style={{
            width: `${100 * zoomScale}%`,
            height: `${totalHeight}px`,
            minHeight: '200px',
          }}
        >
          {flamegraphData.spans.map(layoutSpan => {
            const isSelected = layoutSpan.span.span_id === selectedSpanId;
            const isHovered = layoutSpan.span.span_id === hoveredSpanId;

            // Apply zoom transformation
            const transformed = transformToZoom(
              layoutSpan.leftPercent,
              layoutSpan.widthPercent
            );

            // Skip if outside zoom range or too narrow
            if (!transformed || transformed.widthPercent < 0.1) return null;

            const top = layoutSpan.depth * (rowHeight + rowGap);

            return (
              <button
                key={layoutSpan.span.span_id}
                type='button'
                onClick={() => onSelectSpanId(layoutSpan.span.span_id)}
                onDoubleClick={e => {
                  e.stopPropagation();
                  // Zoom to this span's time range
                  setZoomStart(layoutSpan.leftPercent);
                  setZoomEnd(layoutSpan.leftPercent + layoutSpan.widthPercent);
                }}
                onMouseEnter={e => {
                  setHoveredSpanId(layoutSpan.span.span_id);

                  if (!containerRef.current) return;

                  // Get cursor position
                  const cursorX = e.clientX;
                  const cursorY = e.clientY;

                  // Get container bounds
                  const containerRect =
                    containerRef.current.getBoundingClientRect();

                  // Calculate available space in each direction
                  const spaceRight = containerRect.right - cursorX;
                  const spaceBelow = containerRect.bottom - cursorY;

                  // Determine positioning
                  // Tooltip is roughly 400-600px wide and 200-400px tall
                  const tooltipWidth = 450;
                  const tooltipHeight = 300;

                  const showLeft = spaceRight < tooltipWidth / 2 + 20;
                  const showAbove = spaceBelow < tooltipHeight + 20;

                  setTooltipPosition({
                    x: cursorX,
                    y: cursorY,
                    showLeft,
                    showAbove,
                  });
                }}
                onMouseMove={e => {
                  if (!hoveredSpanId || !containerRef.current) return;

                  // Update position on mouse move
                  const cursorX = e.clientX;
                  const cursorY = e.clientY;

                  const containerRect =
                    containerRef.current.getBoundingClientRect();

                  const spaceRight = containerRect.right - cursorX;
                  const spaceBelow = containerRect.bottom - cursorY;

                  const tooltipWidth = 450;
                  const tooltipHeight = 300;

                  const showLeft = spaceRight < tooltipWidth / 2 + 20;
                  const showAbove = spaceBelow < tooltipHeight + 20;

                  setTooltipPosition({
                    x: cursorX,
                    y: cursorY,
                    showLeft,
                    showAbove,
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
                      ? 'border-white z-10 shadow-md'
                      : 'border-black/20 hover:shadow-md'
                }`}
                style={{
                  left: `${transformed.leftPercent}%`,
                  width: `${transformed.widthPercent}%`,
                  top: `${top}px`,
                  height: `${rowHeight}px`,
                  minWidth: '2px',
                }}
              >
                {/* Show text only if there's enough space */}
                {transformed.widthPercent > 3 && (
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
