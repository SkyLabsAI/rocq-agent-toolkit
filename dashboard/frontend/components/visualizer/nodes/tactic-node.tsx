'use client';

import { Handle, type NodeProps, Position } from '@xyflow/react';

import type { TacticGraphEdge, TacticGraphNode } from '@/services/dataservice';

export type TacticNodeData = {
  node: TacticGraphNode;
  hasError: boolean;
  isSuccess: boolean;
  connectedEdges: TacticGraphEdge[];
};

const TacticNode = (props: NodeProps) => {
  const data = props.data as TacticNodeData;
  const selected = props.selected;
  const { node, hasError } = data;

  const base =
    'rounded-full border-2 shadow-[0px_1px_4px_0px_rgba(0,0,0,0.08)] relative w-12 h-12 flex items-center justify-center';

  const border = hasError
    ? 'border-border-warning'
    : selected
      ? 'border-border-bold'
      : 'border-border-bold';

  const bg = hasError ? 'bg-background-warning' : 'bg-elevation-surface-raised';

  return (
    <div className={`${base} ${border} ${bg}`}>
      <Handle
        type='target'
        position={Position.Left}
        style={{
          width: 8,
          height: 8,
          background: 'var(--color-border-bold)',
          border: 'none',
          left: 0,
          top: '50%',
          transform: 'translate(-50%, -50%)',
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
          right: 0,
          top: '50%',
          transform: 'translate(50%, -50%)',
        }}
      />

      {/* Error badge */}
      {hasError && (
        <div className='absolute -left-2 -top-2 w-5 h-5 rounded-full bg-background-warning border-2 border-border-warning flex items-center justify-center text-[10px] font-bold text-text-warning'>
          ⚠
        </div>
      )}
    </div>
  );
};

export default TacticNode;
