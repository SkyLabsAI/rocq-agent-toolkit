'use client';

import { BaseEdge, EdgeLabelRenderer, type EdgeProps } from '@xyflow/react';

// Configuration: Easy to tweak edge and label positioning
const CONFIG = {
  // Edge positioning
  nodeRadius: 24,
  horizontalShift: 24, // How far left to shift the entire edge path
  baseHeight: 60, // Initial vertical height of the first loop
  heightIncrement: 80, // Vertical spacing between multiple loops on same node

  // Label positioning (independent from edge height)
  labelBaseHeight: 60 - 24 / 2, // Initial vertical height for label positioning
  labelHeightIncrement: 60, // Vertical spacing for labels between multiple loops
  labelOffsetX: 0, // Horizontal offset: positive = right, negative = left
  labelOffsetY: 0, // Vertical offset: positive = down, negative = up
};

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

  const startX = sourceX - CONFIG.nodeRadius - CONFIG.horizontalShift;
  const startY = sourceY;
  const endX = sourceX + CONFIG.nodeRadius - CONFIG.horizontalShift;
  const endY = sourceY;

  const edgeHeight = CONFIG.baseHeight + offset * CONFIG.heightIncrement;
  const labelHeight =
    CONFIG.labelBaseHeight + offset * CONFIG.labelHeightIncrement;

  const control1X = startX;
  const control1Y = startY - edgeHeight;
  const control2X = endX;
  const control2Y = endY - edgeHeight;

  const path = `
    M ${startX},${startY}
    C ${control1X},${control1Y} ${control2X},${control2Y} ${endX},${endY}
  `;

  // Label position: adjust labelOffsetX and labelOffsetY to position label on the edge
  const labelX = sourceX - CONFIG.horizontalShift + CONFIG.labelOffsetX;
  const labelY = sourceY - labelHeight + CONFIG.labelOffsetY;

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
