'use client';

import { Handle, type NodeProps, Position } from '@xyflow/react';

import type { TacticGraphEdge, TacticGraphNode } from '@/services/dataservice';

export type TacticNodeData = {
  node: TacticGraphNode;
  hasError: boolean;
  connectedEdges: TacticGraphEdge[];
};

const TacticNode = (props: NodeProps) => {
  const data = props.data as TacticNodeData;
  const selected = props.selected;
  const { node, hasError } = data;

  const base =
    'rounded-lg border-2 px-3 py-2 shadow-[0px_1px_4px_0px_rgba(0,0,0,0.08)] relative min-w-[200px]';

  const border = hasError
    ? 'border-border-warning'
    : selected
      ? 'border-border-bold'
      : 'border-border-bold';

  const bg = hasError ? 'bg-background-warning' : 'bg-elevation-surface-raised';

  return (
    <div className={`${base} ${border} ${bg} w-full`}>
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

      {/* Error badge */}
      {hasError && (
        <div className='absolute -left-2 -top-2 w-5 h-5 rounded-full bg-background-warning border-2 border-border-warning flex items-center justify-center text-[10px] font-bold text-text-warning'>
          ⚠
        </div>
      )}

      {/* Node ID - Full display */}
      <div className='text-[11px] font-mono text-text font-semibold mb-2 break-all'>
        {node.id}
      </div>
    </div>
  );
};

export default TacticNode;
