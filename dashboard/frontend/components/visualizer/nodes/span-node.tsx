'use client';

import { Handle, type NodeProps, Position } from '@xyflow/react';

export type SpanNodeData = {
  name: string;
  service: string;
  durationMs?: number;
  spanIdShort: string;
  nodeValue?: string;
  isOnPath: boolean;
  hasChildren?: boolean;
  isCollapsed?: boolean;
  onToggleCollapse?: () => void;
  depth?: number;
  childCount?: number;
  totalDescendants?: number;
};

const SpanNode = (props: NodeProps) => {
  const data = props.data as SpanNodeData;
  const selected = props.selected;

  // Depth-based border colors
  const getDepthBorderColor = (depth?: number) => {
    if (depth === undefined) return 'border-elevation-surface-overlay';

    const colors = [
      'border-blue-500', // depth 0
      'border-purple-500', // depth 1
      'border-pink-500', // depth 2
      'border-orange-500', // depth 3
      'border-yellow-500', // depth 4
      'border-green-500', // depth 5
    ];

    return colors[depth % colors.length];
  };

  const base =
    'rounded-lg border-2 px-3 py-2 shadow-[0px_1px_4px_0px_rgba(0,0,0,0.08)] relative';
  const border = selected
    ? 'border-border-focused'
    : getDepthBorderColor(data.depth);
  const bg = data.isOnPath
    ? 'bg-background-success'
    : 'bg-elevation-surface-raised';

  return (
    <div className={`${base} ${border} ${bg} w-full h-full`}>
      <Handle
        type='target'
        position={Position.Left}
        style={{
          width: 8,
          height: 8,
          background: 'var(--color-border-bold)',
          border: 'none',
        }}
      />
      <Handle
        type='source'
        position={Position.Right}
        style={{
          width: 8,
          height: 8,
          background: 'var(--color-border-bold)',
          border: 'none',
        }}
      />

      {/* Depth indicator badge */}
      {data.depth !== undefined && (
        <div className='absolute -left-2 -top-2 w-5 h-5 rounded-full bg-elevation-surface-overlay border-2 border-elevation-surface flex items-center justify-center text-[10px] font-bold text-text'>
          {data.depth}
        </div>
      )}

      {/* Collapse/Expand button with child count */}
      {data.hasChildren && (
        <button
          onClick={e => {
            e.stopPropagation();
            data.onToggleCollapse?.();
          }}
          className='absolute -right-2 top-1/2 -translate-y-1/2 min-w-[20px] h-5 px-1 rounded-full bg-primary-default hover:bg-primary-hovered text-white flex items-center justify-center text-xs font-bold border-2 border-elevation-surface shadow-sm transition-colors z-10'
          title={
            data.isCollapsed
              ? `Expand (${data.childCount} direct, ${data.totalDescendants} total children)`
              : `Collapse (${data.childCount} direct children)`
          }
        >
          {data.isCollapsed ? (
            <span className='flex items-center gap-0.5'>
              <span>+</span>
              {data.totalDescendants && data.totalDescendants > 0 && (
                <span className='text-[9px]'>{data.totalDescendants}</span>
              )}
            </span>
          ) : (
            '−'
          )}
        </button>
      )}

      <div className='flex items-start justify-between gap-2'>
        <div className='min-w-0'>
          <div className='text-sm text-text font-semibold truncate'>
            {data.name}
          </div>
          <div className='text-xs text-text-disabled truncate'>
            {data.service}
            {data.nodeValue ? ` • node=${data.nodeValue}` : ''}
          </div>
        </div>
        <div className='shrink-0 text-xs text-text-disabled'>
          {typeof data.durationMs === 'number' ? `${data.durationMs} ms` : ''}
        </div>
      </div>
      <div className='mt-1 text-[11px] text-text-disabled truncate flex items-center justify-between'>
        <span>{data.spanIdShort}</span>
        {data.hasChildren && data.isCollapsed && data.childCount && (
          <span className='text-[10px] bg-elevation-surface-overlay px-1.5 py-0.5 rounded'>
            {data.childCount} child{data.childCount !== 1 ? 'ren' : ''}
          </span>
        )}
      </div>
    </div>
  );
};

export default SpanNode;
