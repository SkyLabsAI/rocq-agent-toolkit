'use client';

import { BaseEdge, EdgeLabelRenderer, type EdgeProps } from '@xyflow/react';

const SelfLoopEdge = ({
  id,
  sourceX,
  sourceY,
  label,
  labelStyle,
  style,
  markerEnd,
  data,
}: EdgeProps) => {
  const offset = (data?.offset as number) || 0;
  const onEdgeClick = (data?.onEdgeClick as (() => void) | undefined) || null;

  // Node dimensions (must match tactic-graph-view.tsx)
  const NODE_WIDTH = 220;
  const NODE_HEIGHT = 120;

  // Get node's top-left corner (using user's modification)
  const nodeLeft = sourceX - NODE_WIDTH;
  const nodeTop = sourceY - NODE_HEIGHT / 3;

  // All loops start and end at the same points on the node's top edge
  const startX = nodeLeft + 30; // Fixed start point (30px from left edge)
  const endX = nodeLeft + NODE_WIDTH - 30; // Fixed end point (30px from right edge)
  const y = nodeTop;

  // Each loop gets progressively larger radius (stacks vertically)
  const baseRadius = 40;
  const radiusIncrement = 100; // Each loop adds 25px to radius
  const loopRadius = baseRadius + offset * radiusIncrement;

  // Create circular arc - control points determine the height
  const centerX = (startX + endX) / 2;
  const path = `
    M ${startX},${y}
    Q ${centerX},${y - loopRadius} ${endX},${y}
  `;

  // Label at the apex of each loop (different heights for each)
  const labelX = centerX;
  const labelY = y - loopRadius / 2;

  return (
    <>
      <BaseEdge id={id} path={path} style={style} markerEnd={markerEnd} />
      {label && (
        <EdgeLabelRenderer>
          <div
            style={{
              position: 'absolute',
              transform: `translate(-50%, -50%) translate(${labelX}px,${labelY}px)`,
              pointerEvents: 'all',
              fontSize: 10,
              fontWeight: 500,
              cursor: 'pointer',
              ...labelStyle,
            }}
            className='nodrag nopan bg-elevation-surface px-2 py-1 rounded border border-elevation-surface-overlay hover:bg-elevation-surface-overlay transition-colors shadow-sm'
            onClick={e => {
              e.stopPropagation();
              if (onEdgeClick) {
                onEdgeClick();
              }
            }}
          >
            {label}
          </div>
        </EdgeLabelRenderer>
      )}
    </>
  );
};

export default SelfLoopEdge;
