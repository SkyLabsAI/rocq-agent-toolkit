'use client';

import React, { useEffect, useMemo } from 'react';
import dagre from 'dagre';
import {
  Background,
  Controls,
  ReactFlow,
  type Edge,
  type Node,
  type NodeMouseHandler,
  useEdgesState,
  useNodesState,
} from '@xyflow/react';

import type { VisualizerSpanLite } from '@/services/visualizer';
import SpanNode, { type SpanNodeData } from '@/components/visualizer/nodes/span-node';

type Props = {
  spans: VisualizerSpanLite[];
  selectedSpanId?: string;
  onSelectSpanId: (spanId: string) => void;
  successPathNodes: Set<string>;
};

const NODE_W = 260;
const NODE_H = 78;

export default function SpanGraphView({
  spans,
  selectedSpanId,
  onSelectSpanId,
  successPathNodes,
}: Props) {
  const computed = useMemo(() => {
    const nodes: Array<Node<SpanNodeData>> = [];
    const edges: Edge[] = [];

    const ids = new Set(spans.map(s => s.span_id));
    for (const s of spans) {
      const nodeVal =
        typeof s.attributes?.['node'] === 'string'
          ? (s.attributes?.['node'] as string)
          : undefined;
      const isOnPath = nodeVal ? successPathNodes.has(nodeVal) : false;
      const spanShort =
        s.span_id.length > 12 ? `${s.span_id.slice(0, 12)}…` : s.span_id;

      nodes.push({
        id: s.span_id,
        type: 'spanNode',
        position: { x: 0, y: 0 },
        data: {
          name: s.name,
          service: s.service_name,
          durationMs: durationMs(s.start_time_unix_nano, s.end_time_unix_nano),
          spanIdShort: spanShort,
          nodeValue: nodeVal,
          isOnPath,
        },
        width: NODE_W,
        height: NODE_H,
        selected: selectedSpanId === s.span_id,
      });

      const p = s.parent_span_id ?? undefined;
      if (p && ids.has(p)) {
        edges.push({
          id: `${p}→${s.span_id}`,
          source: p,
          target: s.span_id,
          animated: isOnPath,
          style: {
            stroke: isOnPath
              ? 'var(--color-border-success, #6a9a23)'
              : 'var(--color-border-bold, #7d818a)',
            strokeWidth: isOnPath ? 2 : 1.5,
          },
        });
      }
    }

    return layoutDagre(nodes, edges);
  }, [spans, successPathNodes, selectedSpanId]);

  const [nodes, setNodes, onNodesChange] = useNodesState<Node<SpanNodeData>>(
    []
  );
  const [edges, setEdges, onEdgesChange] = useEdgesState<Edge>([]);

  useEffect(() => {
    setNodes(computed.nodes);
  }, [computed.nodes, setNodes]);

  useEffect(() => {
    setEdges(computed.edges);
  }, [computed.edges, setEdges]);

  useEffect(() => {
    setNodes(prev => prev.map(n => ({ ...n, selected: n.id === selectedSpanId })));
  }, [selectedSpanId, setNodes]);

  const onNodeClick: NodeMouseHandler = (_evt, node) => {
    onSelectSpanId(node.id);
  };

  if (!spans.length) {
    return <div className='text-sm text-text-disabled'>No spans to render.</div>;
  }

  if (spans.length > 1000) {
    return (
      <div className='text-sm text-text-danger'>
        Too many spans to render as a graph ({spans.length}). Narrow the trace
        selection.
      </div>
    );
  }

  return (
    <div className='w-full h-full rounded-lg border border-elevation-surface-overlay overflow-hidden bg-elevation-surface-sunken'>
      <ReactFlow
        nodes={nodes}
        edges={edges}
        onNodeClick={onNodeClick}
        fitView
        fitViewOptions={{ padding: 0.2 }}
        nodesDraggable
        nodesConnectable={false}
        elementsSelectable
        nodeTypes={{ spanNode: SpanNode }}
        panOnDrag
        onNodesChange={onNodesChange}
        onEdgesChange={onEdgesChange}
      >
        <Background gap={18} size={1} color='var(--color-border)' />
        <Controls showInteractive={false} />
      </ReactFlow>
    </div>
  );
}

function durationMs(
  startNs?: string | null,
  endNs?: string | null
): number | undefined {
  if (!startNs || !endNs) return undefined;
  const s = Number(startNs);
  const e = Number(endNs);
  if (!Number.isFinite(s) || !Number.isFinite(e)) return undefined;
  const d = e - s;
  if (d < 0) return undefined;
  return Math.round((d / 1_000_000) * 100) / 100;
}

function layoutDagre<T extends Record<string, unknown>>(
  nodes: Array<Node<T>>,
  edges: Edge[]
) {
  const g = new dagre.graphlib.Graph();
  g.setGraph({ rankdir: 'LR', nodesep: 30, ranksep: 70 });
  g.setDefaultEdgeLabel(() => ({}));

  for (const n of nodes) g.setNode(n.id, { width: NODE_W, height: NODE_H });
  for (const e of edges) g.setEdge(e.source, e.target);

  dagre.layout(g);

  const outNodes: Array<Node<T>> = nodes.map(n => {
    const p = g.node(n.id);
    return {
      ...n,
      position: { x: p.x - NODE_W / 2, y: p.y - NODE_H / 2 },
    };
  });

  return { nodes: outNodes, edges };
}


