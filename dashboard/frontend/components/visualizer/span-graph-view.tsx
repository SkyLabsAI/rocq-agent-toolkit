'use client';

import {
  Background,
  Controls,
  type Edge,
  type Node,
  type NodeMouseHandler,
  ReactFlow,
  useEdgesState,
  useNodesState,
} from '@xyflow/react';
import dagre from 'dagre';
import { useEffect, useMemo } from 'react';

import SpanNode, {
  type SpanNodeData,
} from '@/components/visualizer/nodes/span-node';
import { NODE_STYLE_CONFIG } from '@/components/visualizer/nodes/span-node';
import type { EnhancedSpan } from '@/services/visualizer/process-tree';

type Props = {
  spans: EnhancedSpan[];
  selectedSpanId?: string;
  onSelectSpanId: (spanId: string) => void;
  successPathNodes: Set<string>;
  collapsedNodes: Set<string>;
  onToggleCollapse: (spanId: string) => void;
};

const NODE_W = 260;
const NODE_H = 78;

const SpanGraphView = ({
  spans,
  selectedSpanId,
  onSelectSpanId,
  successPathNodes,
  collapsedNodes,
  onToggleCollapse,
}: Props) => {
  const computed = useMemo(() => {
    const nodes: Array<Node<SpanNodeData>> = [];
    const edges: Edge[] = [];

    const ids = new Set(spans.map(s => s.span_id));

    // Build a map of parent -> children for checking if node has children
    const childrenMap = new Map<string, string[]>();
    for (const s of spans) {
      const p = s.parent_span_id ?? undefined;
      if (p) {
        if (!childrenMap.has(p)) {
          childrenMap.set(p, []);
        }
        childrenMap.get(p)!.push(s.span_id);
      }
    }

    // Calculate depths for all nodes
    const depthMap = new Map<string, number>();
    const calculateDepth = (
      spanId: string,
      visited = new Set<string>()
    ): number => {
      if (depthMap.has(spanId)) return depthMap.get(spanId)!;
      if (visited.has(spanId)) return 0;

      visited.add(spanId);
      const span = spans.find(s => s.span_id === spanId);
      if (!span || !span.parent_span_id) {
        depthMap.set(spanId, 0);
        return 0;
      }

      const parentDepth = calculateDepth(span.parent_span_id, visited);
      const depth = parentDepth + 1;
      depthMap.set(spanId, depth);
      return depth;
    };

    for (const s of spans) {
      calculateDepth(s.span_id);
    }

    // Get all descendants of a node
    const getDescendants = (spanId: string): Set<string> => {
      const descendants = new Set<string>();
      const queue = [spanId];
      while (queue.length > 0) {
        const current = queue.shift()!;
        const children = childrenMap.get(current) || [];
        for (const child of children) {
          descendants.add(child);
          queue.push(child);
        }
      }
      return descendants;
    };

    // Filter out collapsed descendants
    const visibleSpanIds = new Set<string>();
    for (const s of spans) {
      // Check if any ancestor is collapsed
      let isHidden = false;
      let current = s.parent_span_id;
      while (current) {
        if (collapsedNodes.has(current)) {
          isHidden = true;
          break;
        }
        const parent = spans.find(sp => sp.span_id === current);
        current = parent?.parent_span_id;
      }
      if (!isHidden) {
        visibleSpanIds.add(s.span_id);
      }
    }

    // Build a map of span_id -> span for quick lookup
    const spanMap = new Map<string, EnhancedSpan>();
    for (const s of spans) {
      spanMap.set(s.span_id, s);
    }

    // Find all success path edges by backtracking from success nodes
    const successPathEdgeIds = new Set<string>();
    // Find all error path edges by backtracking from error nodes
    const errorPathEdgeIds = new Set<string>();

    for (const s of spans) {
      if (!visibleSpanIds.has(s.span_id)) continue;

      const nodeVal =
        typeof s.attributes?.['node'] === 'string'
          ? (s.attributes?.['node'] as string)
          : undefined;
      const isOnPath = nodeVal ? successPathNodes.has(nodeVal) : false;
      const isSuccessProcess = s.processState === 'success';
      const isErrorProcess = s.processState === 'error' || s.virtualErrorNode;

      // If this node is on the success path (either via node attribute or process state),
      // backtrack to root and mark all edges
      if (isOnPath || isSuccessProcess) {
        let current = s.span_id;
        while (current) {
          const span = spanMap.get(current);
          if (!span || !span.parent_span_id) break;

          const parentId = span.parent_span_id;
          // Only mark edges if both parent and child are visible
          if (visibleSpanIds.has(parentId) && visibleSpanIds.has(current)) {
            const edgeId = `${parentId}→${current}`;
            successPathEdgeIds.add(edgeId);
          }

          current = parentId;
        }
      }

      // If this node is an error (process state or virtual error),
      // backtrack to root and mark all edges
      if (isErrorProcess) {
        let current = s.span_id;
        while (current) {
          const span = spanMap.get(current);
          if (!span || !span.parent_span_id) break;

          const parentId = span.parent_span_id;
          // Only mark edges if both parent and child are visible
          if (visibleSpanIds.has(parentId) && visibleSpanIds.has(current)) {
            const edgeId = `${parentId}→${current}`;
            errorPathEdgeIds.add(edgeId);
          }

          current = parentId;
        }
      }
    }

    for (const s of spans) {
      if (!visibleSpanIds.has(s.span_id)) continue;

      const nodeVal =
        typeof s.attributes?.['node'] === 'string'
          ? (s.attributes?.['node'] as string)
          : undefined;
      const isOnPath = nodeVal ? successPathNodes.has(nodeVal) : false;
      const spanShort =
        s.span_id.length > 12 ? `${s.span_id.slice(0, 12)}…` : s.span_id;
      const children = childrenMap.get(s.span_id) || [];
      const hasChildren = children.length > 0;
      const isCollapsed = collapsedNodes.has(s.span_id);
      const depth = depthMap.get(s.span_id) || 0;

      // Count total descendants (for showing in collapsed state)
      const totalDescendants = getDescendants(s.span_id).size;

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
          hasChildren,
          isCollapsed,
          onToggleCollapse: () => onToggleCollapse(s.span_id),
          depth,
          childCount: children.length,
          totalDescendants,
          isProcessNode: s.isProcessNode,
          processState: s.processState,
          virtualErrorNode: s.virtualErrorNode,
        },
        width: NODE_W,
        height: NODE_H,
        selected: selectedSpanId === s.span_id,
      });

      const p = s.parent_span_id ?? undefined;
      if (p && ids.has(p) && visibleSpanIds.has(p)) {
        const edgeId = `${p}→${s.span_id}`;
        const isSuccessEdge = successPathEdgeIds.has(edgeId);
        const isErrorEdge = errorPathEdgeIds.has(edgeId);

        // Priority: success > error > intermediate
        // If an edge is on both success and error paths, show success color
        const edgeStyle = isSuccessEdge
          ? NODE_STYLE_CONFIG.success.edge
          : isErrorEdge
            ? NODE_STYLE_CONFIG.error.edge
            : NODE_STYLE_CONFIG.intermediate.edge;

        // Extract action from span attributes
        const action =
          typeof s.attributes?.action === 'string'
            ? (s.attributes.action as string)
            : undefined;

        // Determine label border color based on edge type
        const labelBgStyle: {
          fill: string;
          fillOpacity: number;
          stroke?: string;
          strokeWidth?: number;
        } = {
          fill: 'var(--color-elevation-surface, #ffffff)',
          fillOpacity: 0.9,
        };

        // Add colored border for success and error edges
        if (isSuccessEdge) {
          labelBgStyle.stroke = 'var(--color-border-success, #6a9a23)';
          labelBgStyle.strokeWidth = 1.5;
        } else if (isErrorEdge) {
          labelBgStyle.stroke = 'var(--color-border-warning, #d97706)';
          labelBgStyle.strokeWidth = 1.5;
        }

        edges.push({
          id: edgeId,
          source: p,
          target: s.span_id,
          label: action,
          labelStyle: {
            fontSize: 11,
            fontWeight: 500,
            fill: 'var(--color-text-subtle, #7d818a)',
          },
          labelBgStyle,
          labelBgPadding: [4, 6],
          labelBgBorderRadius: 4,
          animated: edgeStyle.animated,
          style: {
            stroke: edgeStyle.stroke,
            strokeWidth: edgeStyle.strokeWidth,
          },
        });
      }
    }

    return layoutDagre(nodes, edges);
  }, [
    spans,
    successPathNodes,
    selectedSpanId,
    collapsedNodes,
    onToggleCollapse,
  ]);

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
    setNodes(prev =>
      prev.map(n => ({ ...n, selected: n.id === selectedSpanId }))
    );
  }, [selectedSpanId, setNodes]);

  const onNodeClick: NodeMouseHandler = (_evt, node) => {
    onSelectSpanId(node.id);
  };

  if (!spans.length) {
    return (
      <div className='text-sm text-text-disabled'>No spans to render.</div>
    );
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
};

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

  // Calculate spacing based on label lengths
  // Estimate: ~6.5 pixels per character for font size 11 (variable-width font)
  // Plus padding: labelBgPadding [4, 6] = 8px vertical, 12px horizontal
  const estimateLabelWidth = (label: string | undefined): number => {
    if (!label) return 0;
    // Character width estimate + horizontal padding (6px * 2) + some buffer
    return label.length * 6.5 + 12 + 8;
  };

  // Calculate required spacing for each edge based on its label
  const edgeSpacingMap = new Map<string, number>();
  const baseRanksep = 70;
  const baseNodesep = 30;

  for (const edge of edges) {
    const labelWidth = estimateLabelWidth(edge.label as string | undefined);

    // Calculate required spacing: need space for label between nodes
    // The label appears between nodes, so we need:
    // - Small buffer from source node (to avoid overlap)
    // - Full label width
    // - Small buffer to target node (to avoid overlap)
    // Use a more conservative approach: only add extra space if label is significant
    const nodeBuffer = 20; // Small buffer to clear node edges
    const padding = 10; // Minimal padding for readability
    const requiredSpacing =
      labelWidth > 0
        ? nodeBuffer + labelWidth + nodeBuffer + padding
        : baseRanksep; // No label, use base spacing

    edgeSpacingMap.set(edge.id, requiredSpacing);
  }

  // Use base spacing for dagre initial layout
  g.setGraph({ rankdir: 'LR', nodesep: baseNodesep, ranksep: baseRanksep });
  g.setDefaultEdgeLabel(() => ({}));

  for (const n of nodes) g.setNode(n.id, { width: NODE_W, height: NODE_H });
  for (const e of edges) g.setEdge(e.source, e.target);

  dagre.layout(g);

  // Post-process: adjust positions based on edge label widths
  // Build a map of source -> target edges to find rank transitions
  const edgesBySource = new Map<string, Edge[]>();
  for (const edge of edges) {
    if (!edgesBySource.has(edge.source)) {
      edgesBySource.set(edge.source, []);
    }
    edgesBySource.get(edge.source)!.push(edge);
  }

  // Get initial positions
  const initialPositions = new Map<string, { x: number; y: number }>();
  for (const n of nodes) {
    const p = g.node(n.id);
    initialPositions.set(n.id, { x: p.x, y: p.y });
  }

  // Calculate ranks from x positions (dagre's layout)
  const nodeRanks = new Map<string, number>();
  const xValues = Array.from(initialPositions.values())
    .map(p => p.x)
    .sort((a, b) => a - b);

  // Cluster x positions into ranks
  const rankThreshold = baseRanksep * 0.4;
  const rankClusters: number[][] = [];
  let currentCluster: number[] = [xValues[0]];

  for (let i = 1; i < xValues.length; i++) {
    if (xValues[i] - xValues[i - 1] < rankThreshold) {
      currentCluster.push(xValues[i]);
    } else {
      rankClusters.push(currentCluster);
      currentCluster = [xValues[i]];
    }
  }
  rankClusters.push(currentCluster);

  // Map nodes to ranks
  const nodesByRank = new Map<number, string[]>();
  for (const n of nodes) {
    const pos = initialPositions.get(n.id)!;
    let rank = 0;
    let minDist = Infinity;
    for (let r = 0; r < rankClusters.length; r++) {
      const cluster = rankClusters[r];
      const clusterCenter = cluster.reduce((a, b) => a + b, 0) / cluster.length;
      const dist = Math.abs(pos.x - clusterCenter);
      if (dist < minDist) {
        minDist = dist;
        rank = r;
      }
    }
    nodeRanks.set(n.id, rank);
    if (!nodesByRank.has(rank)) {
      nodesByRank.set(rank, []);
    }
    nodesByRank.get(rank)!.push(n.id);
  }

  // Adjust positions rank by rank
  const adjustedPositions = new Map<string, { x: number; y: number }>();
  const sortedRanks = Array.from(nodesByRank.keys()).sort((a, b) => a - b);
  let cumulativeOffset = 0;

  for (let i = 0; i < sortedRanks.length; i++) {
    const rank = sortedRanks[i];
    const nodesInRank = nodesByRank.get(rank)!;

    if (i > 0) {
      // Find max spacing needed for edges entering this rank
      let maxSpacingNeeded = baseRanksep;
      for (const nodeId of nodesInRank) {
        const incomingEdges = edges.filter(e => e.target === nodeId);
        for (const edge of incomingEdges) {
          const requiredSpacing = edgeSpacingMap.get(edge.id) || baseRanksep;
          maxSpacingNeeded = Math.max(maxSpacingNeeded, requiredSpacing);
        }
      }
      // Add the difference to cumulative offset
      cumulativeOffset += maxSpacingNeeded - baseRanksep;
    }

    // Apply offset to all nodes in this rank
    for (const nodeId of nodesInRank) {
      const pos = initialPositions.get(nodeId)!;
      adjustedPositions.set(nodeId, {
        x: pos.x + cumulativeOffset,
        y: pos.y,
      });
    }
  }

  const outNodes: Array<Node<T>> = nodes.map(n => {
    const adjustedPos =
      adjustedPositions.get(n.id) || initialPositions.get(n.id)!;
    return {
      ...n,
      position: {
        x: adjustedPos.x - NODE_W / 2,
        y: adjustedPos.y - NODE_H / 2,
      },
    };
  });

  return { nodes: outNodes, edges };
}

export default SpanGraphView;
