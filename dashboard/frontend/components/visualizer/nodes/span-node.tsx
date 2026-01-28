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
  isProcessNode?: boolean;
  processState?: 'root' | 'intermediate' | 'error' | 'success';
  virtualErrorNode?: boolean;
};

// Single configuration object for all node and edge styling
// Only 3 states: error, success, and intermediate
export const NODE_STYLE_CONFIG = {
  error: {
    bg: 'bg-background-warning',
    border: 'border-border-warning',
    textColor: 'text-text-warning',
    badgeBg: 'bg-background-warning',
    badgeBorder: 'border-border-warning',
    icon: '⚠',
    // Edge styling for error path
    edge: {
      stroke: 'var(--color-border-warning, #d97706)',
      strokeWidth: 2,
      animated: false,
    },
  },
  success: {
    bg: 'bg-background-success',
    border: 'border-border-success',
    textColor: 'text-text-success',
    badgeBg: 'bg-background-success',
    badgeBorder: 'border-border-success',
    icon: '✓',
    // Edge styling for success path
    edge: {
      stroke: 'var(--color-border-success, #6a9a23)',
      strokeWidth: 2,
      animated: true,
    },
  },
  intermediate: {
    bg: 'bg-elevation-surface-raised',
    border: 'border-border-bold',
    textColor: 'text-text-subtle',
    badgeBg: 'bg-elevation-surface-overlay',
    badgeBorder: 'border-border-bold',
    icon: '→',
    // Edge styling for intermediate path
    edge: {
      stroke: 'var(--color-border-bold, #7d818a)',
      strokeWidth: 1.5,
      animated: false,
    },
  },
  // Selected state uses a prominent blue/primary border with glow
  selected: {
    border: 'border-primary-default',
    ringClass: 'ring-4 ring-primary-default/30',
  },
} as const;

const SpanNode = (props: NodeProps) => {
  const data = props.data as SpanNodeData;
  const selected = props.selected;

  // Determine node state: error > success > intermediate
  const getNodeState = (): 'error' | 'success' | 'intermediate' => {
    // Check for error states first
    if (data.virtualErrorNode) return 'error';
    if (data.processState === 'error') return 'error';

    // Check for success states
    if (data.processState === 'success') return 'success';
    if (data.isOnPath) return 'success';

    // Everything else is intermediate
    return 'intermediate';
  };

  const nodeState = getNodeState();
  const nodeStyle = NODE_STYLE_CONFIG[nodeState];

  // Get badge icon from config
  const getBadgeIcon = () => {
    return nodeStyle.icon;
  };

  // Determine border color (priority: selected > state-based)
  const border = selected
    ? NODE_STYLE_CONFIG.selected.border
    : nodeStyle.border;

  // Add ring effect for selected state
  const ringClass = selected ? NODE_STYLE_CONFIG.selected.ringClass : '';

  // Add scale and enhanced shadow for selected state
  const selectedEnhancement = selected
    ? 'scale-105 shadow-[0px_4px_12px_0px_rgba(59,130,246,0.3)]'
    : '';

  // Determine background color (based on state)
  const bg = nodeStyle.bg;

  const base =
    'rounded-lg border-2 px-3 py-2 shadow-[0px_1px_4px_0px_rgba(0,0,0,0.08)] relative transition-all duration-200';

  return (
    <div
      className={`${base} ${border} ${bg} ${ringClass} ${selectedEnhancement} w-full h-full`}
    >
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
      {data.depth !== undefined && !data.isProcessNode && (
        <div className='absolute -left-2 -top-2 w-5 h-5 rounded-full bg-elevation-surface-overlay border-2 border-elevation-surface flex items-center justify-center text-[10px] font-bold text-text'>
          {data.depth}
        </div>
      )}

      {/* Process state badge */}
      {data.isProcessNode && (
        <div
          className={`absolute -left-2 -top-2 px-2 h-5 rounded-full ${nodeStyle.badgeBg} border-2 ${nodeStyle.badgeBorder} flex items-center justify-center text-[10px] font-bold ${nodeStyle.textColor}`}
        >
          {getBadgeIcon()}
        </div>
      )}

      {/* Collapse/Expand button with child count */}
      {data.hasChildren && (
        <button
          onClick={e => {
            e.stopPropagation();
            data.onToggleCollapse?.();
          }}
          className='absolute -right-2 top-1/2 -translate-y-1/2 min-w-[20px] h-5 px-1 rounded-full bg-primary-default hover:bg-primary-hovered text-text-inverse flex items-center justify-center text-xs font-bold border-2 border-elevation-surface shadow-sm transition-colors z-10'
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
