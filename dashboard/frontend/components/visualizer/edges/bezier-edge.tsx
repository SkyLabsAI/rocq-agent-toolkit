'use client';

import { BaseEdge, EdgeLabelRenderer, type EdgeProps, getBezierPath } from '@xyflow/react';

const BezierEdge = ({
  id,
  sourceX,
  sourceY,
  targetX,
  targetY,
  sourcePosition,
  targetPosition,
  label,
  labelStyle,
  labelBgStyle,
  style,
  markerEnd,
  data,
}: EdgeProps) => {
  const onEdgeClick = (data?.onEdgeClick as (() => void) | undefined) || null;
  const pathOptions = (data?.pathOptions as { borderRadius?: number; curvature?: number }) || {};

  const [edgePath, labelX, labelY] = getBezierPath({
    sourceX,
    sourceY,
    sourcePosition,
    targetX,
    targetY,
    targetPosition,
    curvature: pathOptions.curvature || 0.5,
  });

  return (
    <>
      <BaseEdge id={id} path={edgePath} style={style} markerEnd={markerEnd} />
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
            className='nodrag nopan px-2 py-1 rounded border transition-colors shadow-sm'
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

export default BezierEdge;
