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
  // For self-loops, create a circular path at the top of the node
  // Get the offset for multiple self-loops on the same node
  const offset = (data?.offset as number) || 0;

  // Node dimensions (should match NODE_W and NODE_H in tactic-graph-view)
  const nodeWidth = 220;
  const nodeHeight = 120;

  // Loop parameters
  const loopHeight = 50; // Height of the loop above the node
  const loopWidth = 40; // Width of each loop
  const horizontalSpacing = 50; // Horizontal spacing between loops

  // Calculate horizontal offset for multiple loops
  const horizontalOffset = offset * horizontalSpacing;

  // Starting point: top-left of node, offset horizontally for each loop
  const startX = sourceX - nodeWidth / 2 + 30 + horizontalOffset;
  const startY = sourceY - nodeHeight / 2;

  // End point: slightly to the right of start point
  const endX = startX + loopWidth;
  const endY = startY;

  // Control points for a smooth loop above the node
  const controlPoint1X = startX;
  const controlPoint1Y = startY - loopHeight;
  const controlPoint2X = endX;
  const controlPoint2Y = startY - loopHeight;

  // Create a smooth loop path using cubic Bezier
  const path = `
    M ${startX},${startY}
    C ${controlPoint1X},${controlPoint1Y} 
      ${controlPoint2X},${controlPoint2Y} 
      ${endX},${endY}
  `;

  // Position for the label - place it at the top of the loop
  const labelX = (startX + endX) / 2;
  const labelY = startY - loopHeight - 10;

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
            className='nodrag nopan bg-elevation-surface px-2 py-1 rounded border border-elevation-surface-overlay hover:bg-elevation-surface-overlay transition-colors'
            onClick={e => {
              e.stopPropagation();
              // The edge click will be handled by ReactFlow's onEdgeClick
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
