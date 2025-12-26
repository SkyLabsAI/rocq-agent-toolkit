'use client';

import React from 'react';
import { Handle, Position, type NodeProps } from '@xyflow/react';

export type SpanNodeData = {
  name: string;
  service: string;
  durationMs?: number;
  spanIdShort: string;
  nodeValue?: string;
  isOnPath: boolean;
};

export default function SpanNode(props: NodeProps) {
  const data = props.data as SpanNodeData;
  const selected = props.selected;

  const base =
    'rounded-lg border px-3 py-2 shadow-[0px_1px_4px_0px_rgba(0,0,0,0.08)]';
  const border = selected
    ? 'border-border-focused'
    : 'border-elevation-surface-overlay';
  const bg = data.isOnPath ? 'bg-background-success' : 'bg-elevation-surface-raised';

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
      <div className='mt-1 text-[11px] text-text-disabled truncate'>
        {data.spanIdShort}
      </div>
    </div>
  );
}


