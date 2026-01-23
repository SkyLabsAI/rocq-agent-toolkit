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
import { useEffect, useMemo, useRef } from 'react';

import SelfLoopEdge from '@/components/visualizer/edges/self-loop-edge';
import TacticNode, {
  type TacticNodeData,
} from '@/components/visualizer/nodes/tactic-node';
import type { TacticGraphResponse } from '@/services/dataservice';

type Props = {
  graph: TacticGraphResponse;
  selectedNodeId?: string;
  onSelectNodeId: (nodeId: string | null) => void;
  selectedEdgeId?: string;
  onSelectEdgeId: (edgeId: string | null) => void;
};

const NODE_W = 220;
const NODE_H = 120; // Increased to accommodate self-loop edges at the top

const TacticGraphView = ({
  graph,
  selectedNodeId,
  onSelectNodeId,
  selectedEdgeId,
  onSelectEdgeId,
}: Props) => {
  // Use a ref to store the callback to avoid re-creating edges on every selection change
  const onSelectEdgeIdRef = useRef(onSelectEdgeId);
  useEffect(() => {
    onSelectEdgeIdRef.current = onSelectEdgeId;
  }, [onSelectEdgeId]);

  const computed = useMemo(() => {
    const nodes: Array<Node<TacticNodeData>> = [];
    const edges: Edge[] = [];

    // Build a map of node id -> node for quick lookup
    const nodeMap = new Map<string, (typeof graph.graph.nodes)[0]>();
    for (const node of graph.graph.nodes) {
      nodeMap.set(node.id, node);
    }

    // Build a map of node id -> connected edges
    const edgesByNode = new Map<string, Array<(typeof graph.graph.edges)[0]>>();
    const outgoingEdgesByNode = new Map<
      string,
      Array<(typeof graph.graph.edges)[0]>
    >();

    for (const edge of graph.graph.edges) {
      if (!edgesByNode.has(edge.source)) {
        edgesByNode.set(edge.source, []);
      }
      if (!edgesByNode.has(edge.target)) {
        edgesByNode.set(edge.target, []);
      }
      edgesByNode.get(edge.source)!.push(edge);
      edgesByNode.get(edge.target)!.push(edge);

      // Track outgoing edges separately
      if (!outgoingEdgesByNode.has(edge.source)) {
        outgoingEdgesByNode.set(edge.source, []);
      }
      outgoingEdgesByNode.get(edge.source)!.push(edge);
    }

    // Create nodes
    for (const node of graph.graph.nodes) {
      const hasError =
        node.information?.error === 'true' || node.information?.error === true;
      const connectedEdges = edgesByNode.get(node.id) || [];

      // Check if this is an end node (no outgoing edges, excluding self-loops)
      const outgoingEdges = outgoingEdgesByNode.get(node.id) || [];
      const hasNonSelfLoopOutgoing = outgoingEdges.some(
        e => e.target !== node.id
      );
      const isEndNode = !hasNonSelfLoopOutgoing;
      const isSuccess = isEndNode && !hasError;

      nodes.push({
        id: node.id,
        type: 'tacticNode',
        position: { x: 0, y: 0 },
        data: {
          node,
          hasError,
          isSuccess,
          connectedEdges,
        },
        width: NODE_W,
        height: NODE_H,
        selected: selectedNodeId === node.id,
      });
    }

    // Create edges with unique IDs and support for self-loops
    // Group edges by source-target pair to handle multiple edges between same nodes
    const edgeGroups = new Map<string, Array<(typeof graph.graph.edges)[0]>>();
    for (const edge of graph.graph.edges) {
      const key = `${edge.source}→${edge.target}`;
      if (!edgeGroups.has(key)) {
        edgeGroups.set(key, []);
      }
      edgeGroups.get(key)!.push(edge);
    }

    // Create edges with unique IDs
    let edgeIndex = 0;
    for (const [, groupEdges] of edgeGroups) {
      groupEdges.forEach((edge, idx) => {
        const hasError =
          edge.information?.error === 'true' ||
          edge.information?.error === true;

        const isSelfLoop = edge.source === edge.target;
        const edgeId = `edge-${edgeIndex++}`;

        // Truncate label to 100 characters
        const truncatedLabel =
          edge.label.length > 100
            ? `${edge.label.slice(0, 100)}...`
            : edge.label;

        edges.push({
          id: edgeId,
          source: edge.source,
          target: edge.target,
          label: truncatedLabel,
          data: {
            originalEdge: edge,
            edgeId,
            offset: isSelfLoop ? idx : 0, // For multiple self-loops on same node
            onEdgeClick: () => onSelectEdgeIdRef.current(edgeId), // Use ref to avoid dependency
          },
          type: isSelfLoop ? 'selfloop' : undefined,
          labelStyle: {
            fontSize: 10,
            fontWeight: 500,
            fill: hasError
              ? 'var(--color-text-warning, #d97706)'
              : 'var(--color-text-subtle, #7d818a)',
          },
          labelBgStyle: {
            fill: 'var(--color-elevation-surface, #ffffff)',
            fillOpacity: 0.9,
            stroke: hasError
              ? 'var(--color-border-warning, #d97706)'
              : selectedEdgeId === edgeId
                ? 'var(--color-border-bold, #7d818a)'
                : undefined,
            strokeWidth: hasError
              ? 1.5
              : selectedEdgeId === edgeId
                ? 2
                : undefined,
          },
          labelBgPadding: [4, 6],
          labelBgBorderRadius: 4,
          animated: false,
          interactionWidth: 20, // Make the edge easier to click
          style: {
            stroke: hasError
              ? 'var(--color-border-warning, #d97706)'
              : selectedEdgeId === edgeId
                ? 'var(--color-border-bold, #7d818a)'
                : 'var(--color-border, #e5e7eb)',
            strokeWidth: selectedEdgeId === edgeId ? 3 : hasError ? 2 : 1.5,
          },
          markerEnd: {
            type: 'arrowclosed',
            width: 20,
            height: 20,
            color: hasError
              ? 'var(--color-border-warning, #d97706)'
              : selectedEdgeId === edgeId
                ? 'var(--color-border-bold, #7d818a)'
                : 'var(--color-border, #e5e7eb)',
          },
        });
      });
    }

    return layoutDagre(nodes, edges);
  }, [graph]);

  const [nodes, setNodes, onNodesChange] = useNodesState<Node<TacticNodeData>>(
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
      prev.map(n => ({ ...n, selected: n.id === selectedNodeId }))
    );
  }, [selectedNodeId, setNodes]);

  // Update edge selection state without recreating edges
  useEffect(() => {
    setEdges(prev =>
      prev.map(e => {
        const edgeData = e.data as
          | {
              originalEdge?: (typeof graph.graph.edges)[0];
              edgeId?: string;
              offset?: number;
            }
          | undefined;
        const hasError =
          edgeData?.originalEdge?.information?.error === 'true' ||
          edgeData?.originalEdge?.information?.error === true;

        return {
          ...e,
          style: {
            ...e.style,
            strokeWidth: selectedEdgeId === e.id ? 3 : hasError ? 2 : 1.5,
          },
          labelBgStyle: {
            ...e.labelBgStyle,
            stroke: hasError
              ? 'var(--color-border-warning, #d97706)'
              : selectedEdgeId === e.id
                ? 'var(--color-border-bold, #7d818a)'
                : undefined,
            strokeWidth: hasError
              ? 1.5
              : selectedEdgeId === e.id
                ? 2
                : undefined,
          },
        };
      })
    );
  }, [selectedEdgeId, setEdges, graph.graph.edges]);

  const onNodeClick: NodeMouseHandler = (_evt, node) => {
    onSelectNodeId(node.id);
  };

  const onEdgeClick = (_evt: React.MouseEvent, edge: Edge) => {
    onSelectEdgeId(edge.id);
  };

  const onPaneClick = () => {
    // Deselect both nodes and edges when clicking on empty space
    onSelectNodeId(null);
    onSelectEdgeId(null);
  };

  if (!graph.graph.nodes.length) {
    return (
      <div className='text-sm text-text-disabled'>No nodes to render.</div>
    );
  }

  return (
    <div className='w-full h-full rounded-lg border border-elevation-surface-overlay overflow-hidden bg-elevation-surface-sunken'>
      <ReactFlow
        nodes={nodes}
        edges={edges}
        onNodeClick={onNodeClick}
        onEdgeClick={onEdgeClick}
        onPaneClick={onPaneClick}
        fitView
        fitViewOptions={{ padding: 0.2 }}
        nodesDraggable
        nodesConnectable={false}
        elementsSelectable
        nodeTypes={{ tacticNode: TacticNode }}
        edgeTypes={{ selfloop: SelfLoopEdge }}
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

function layoutDagre<T extends Record<string, unknown>>(
  nodes: Array<Node<T>>,
  edges: Edge[]
) {
  const g = new dagre.graphlib.Graph();

  // Calculate spacing based on label lengths
  const estimateLabelWidth = (label: string | undefined): number => {
    if (!label) return 0;
    return label.length * 6.5 + 12 + 8;
  };

  const edgeSpacingMap = new Map<string, number>();
  const baseRanksep = 500; // Increased from 100 to 180 to accommodate 100-char labels
  const baseNodesep = 200; // Increased from 50 to 60 for better vertical spacing

  for (const edge of edges) {
    const labelWidth = estimateLabelWidth(edge.label as string | undefined);
    const nodeBuffer = 20;
    const padding = 10;
    const requiredSpacing =
      labelWidth > 0
        ? nodeBuffer + labelWidth + nodeBuffer + padding
        : baseRanksep;
    edgeSpacingMap.set(edge.id, requiredSpacing);
  }

  g.setGraph({ rankdir: 'LR', nodesep: baseNodesep, ranksep: baseRanksep });
  g.setDefaultEdgeLabel(() => ({}));

  for (const n of nodes) g.setNode(n.id, { width: NODE_W, height: NODE_H });
  for (const e of edges) g.setEdge(e.source, e.target);

  dagre.layout(g);

  const outNodes: Array<Node<T>> = nodes.map(n => {
    const pos = g.node(n.id);
    return {
      ...n,
      position: {
        x: pos.x - NODE_W / 2,
        y: pos.y - NODE_H / 2,
      },
    };
  });

  return { nodes: outNodes, edges };
}

export default TacticGraphView;
