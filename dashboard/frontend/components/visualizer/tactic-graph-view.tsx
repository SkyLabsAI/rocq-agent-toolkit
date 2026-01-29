'use client';

import * as d3 from 'd3';
import { useEffect, useRef } from 'react';

import type { TacticGraphResponse } from '@/services/dataservice';

type Props = {
  graph: TacticGraphResponse;
  selectedNodeId?: string;
  onSelectNodeId: (nodeId: string | null) => void;
  selectedEdgeId?: string;
  onSelectEdgeId: (edgeId: string | null) => void;
};

const NODE_RADIUS = 24; // Circle radius (48px diameter)

// Helper function to clean up insert_command labels
const cleanLabel = (label: string): string => {
  const insertCommandMatch = label.match(/insert_command\((.*)\)/);
  if (insertCommandMatch) {
    return insertCommandMatch[1];
  }
  return label;
};

interface SimNode extends d3.SimulationNodeDatum {
  id: string;
  hasError: boolean;
  isSuccess: boolean;
  x: number;
  y: number;
}

interface SimLink extends d3.SimulationLinkDatum<SimNode> {
  id: string;
  source: string | SimNode;
  target: string | SimNode;
  label: string;
  hasError: boolean;
  isSelfLoop: boolean;
  offset: number;
}

interface ForceLink extends d3.SimulationLinkDatum<SimNode> {
  id: string;
  source: SimNode;
  target: SimNode;
  label: string;
  hasError: boolean;
  isSelfLoop: boolean;
  offset: number;
}

const TacticGraphView = ({
  graph,
  selectedNodeId,
  onSelectNodeId,
  selectedEdgeId,
  onSelectEdgeId,
}: Props) => {
  const svgRef = useRef<SVGSVGElement>(null);
  const simulationRef = useRef<d3.Simulation<SimNode, SimLink> | null>(null);
  const edgePathsRef = useRef<d3.Selection<SVGPathElement, ForceLink, SVGGElement, unknown> | null>(null);
  const selfLoopsRef = useRef<d3.Selection<SVGPathElement, ForceLink, SVGGElement, unknown> | null>(null);
  const selfLoopLabelsRef = useRef<d3.Selection<SVGGElement, ForceLink, SVGGElement, unknown> | null>(null);
  const edgeLabelsRef = useRef<d3.Selection<SVGGElement, ForceLink, SVGGElement, unknown> | null>(null);
  const nodesRef = useRef<d3.Selection<SVGGElement, SimNode, SVGGElement, unknown> | null>(null);
  const isTaskSuccessRef = useRef<boolean>(false);
  const hasRenderedRef = useRef<boolean>(false);

  // Render graph only once
  useEffect(() => {
    if (!svgRef.current || !graph.graph.nodes.length || hasRenderedRef.current) return;
    hasRenderedRef.current = true;

    const svg = d3.select(svgRef.current);
    const width = svgRef.current.clientWidth;
    const height = svgRef.current.clientHeight;

    // Clear previous content
    svg.selectAll('*').remove();

    // Create container group for zoom/pan
    const container = svg.append('g').attr('class', 'graph-container');
    
    // Add zoom and pan behavior
    const zoom = d3.zoom<SVGSVGElement, unknown>()
      .scaleExtent([0.1, 4])
      .on('zoom', (event) => {
        container.attr('transform', event.transform);
      });
    
    svg.call(zoom);

    // Background grid
    const defs = svg.append('defs');
    const pattern = defs.append('pattern')
      .attr('id', 'grid')
      .attr('width', 18)
      .attr('height', 18)
      .attr('patternUnits', 'userSpaceOnUse');
    
    pattern.append('circle')
      .attr('cx', 1)
      .attr('cy', 1)
      .attr('r', 0.5)
      .attr('fill', 'var(--color-border, #e5e7eb)');

    container.append('rect')
      .attr('width', width * 10)
      .attr('height', height * 10)
      .attr('x', -width * 5)
      .attr('y', -height * 5)
      .attr('fill', 'url(#grid)');

    // Arrow markers
    defs.append('marker')
      .attr('id', 'arrow-default')
      .attr('viewBox', '0 0 10 10')
      .attr('refX', 8)
      .attr('refY', 5)
      .attr('markerWidth', 6)
      .attr('markerHeight', 6)
      .attr('orient', 'auto')
      .append('path')
      .attr('d', 'M 0 0 L 10 5 L 0 10 z')
      .attr('fill', 'var(--color-border, #e5e7eb)');

    defs.append('marker')
      .attr('id', 'arrow-success')
      .attr('viewBox', '0 0 10 10')
      .attr('refX', 8)
      .attr('refY', 5)
      .attr('markerWidth', 6)
      .attr('markerHeight', 6)
      .attr('orient', 'auto')
      .append('path')
      .attr('d', 'M 0 0 L 10 5 L 0 10 z')
      .attr('fill', 'var(--color-border-success, #6a9a23)');

    defs.append('marker')
      .attr('id', 'arrow-error')
      .attr('viewBox', '0 0 10 10')
      .attr('refX', 8)
      .attr('refY', 5)
      .attr('markerWidth', 6)
      .attr('markerHeight', 6)
      .attr('orient', 'auto')
      .append('path')
      .attr('d', 'M 0 0 L 10 5 L 0 10 z')
      .attr('fill', 'var(--color-border-warning, #d97706)');

    defs.append('marker')
      .attr('id', 'arrow-selected')
      .attr('viewBox', '0 0 10 10')
      .attr('refX', 8)
      .attr('refY', 5)
      .attr('markerWidth', 6)
      .attr('markerHeight', 6)
      .attr('orient', 'auto')
      .append('path')
      .attr('d', 'M 0 0 L 10 5 L 0 10 z')
      .attr('fill', 'var(--color-border-bold, #7d818a)');

    // Check graph-level task status
    const graphInfo = graph.graph.information;
    const taskStatus = graphInfo?.taskStatus ?? graphInfo?.task_status;
    const isTaskSuccess =
      taskStatus === true ||
      taskStatus === 'true' ||
      String(taskStatus).toLowerCase() === 'true';
    
    isTaskSuccessRef.current = isTaskSuccess;

    // Build edge maps for node analysis
    const outgoingEdgesByNode = new Map<string, any[]>();
    for (const edge of graph.graph.edges) {
      if (!outgoingEdgesByNode.has(edge.source)) {
        outgoingEdgesByNode.set(edge.source, []);
      }
      outgoingEdgesByNode.get(edge.source)!.push(edge);
    }

    // Create simulation nodes with better initial distribution
    const nodeCount = graph.graph.nodes.length;
    const angleStep = (2 * Math.PI) / nodeCount;
    const radius = Math.min(width, height) * 0.3;
    
    const simNodes: SimNode[] = graph.graph.nodes.map((node, index) => {
      const hasError = node.information?.error === 'true' || node.information?.error === true;
      const outgoingEdges = outgoingEdgesByNode.get(node.id) || [];
      const hasNonSelfLoopOutgoing = outgoingEdges.some(e => e.target !== node.id);
      const isEndNode = !hasNonSelfLoopOutgoing;
      const isSuccess = isEndNode && !hasError;

      // Distribute nodes in a circle initially
      const angle = index * angleStep;
      const x = width / 2 + Math.cos(angle) * radius;
      const y = height / 2 + Math.sin(angle) * radius;

      return {
        id: node.id,
        hasError,
        isSuccess,
        x,
        y,
        vx: 0,
        vy: 0,
      };
    });

    // Group edges by source-target pair
    const edgeGroups = new Map<string, any[]>();
    for (const edge of graph.graph.edges) {
      const key = `${edge.source}→${edge.target}`;
      if (!edgeGroups.has(key)) {
        edgeGroups.set(key, []);
      }
      edgeGroups.get(key)!.push(edge);
    }

    // Create simulation links
    const simLinks: SimLink[] = [];
    let edgeIndex = 0;
    for (const [, groupEdges] of edgeGroups) {
      groupEdges.forEach((edge, idx) => {
        const hasError = edge.information?.error === 'true' || edge.information?.error === true;
        const isSelfLoop = edge.source === edge.target;
        const cleanedLabel = cleanLabel(edge.label);
        const truncatedLabel = cleanedLabel.length > 100 
          ? `${cleanedLabel.slice(0, 100)}...` 
          : cleanedLabel;

        simLinks.push({
          id: `edge-${edgeIndex++}`,
          source: edge.source,
          target: edge.target,
          label: truncatedLabel,
          hasError,
          isSelfLoop,
          offset: isSelfLoop ? idx : 0,
        });
      });
    }

    // Create links for force simulation (must reference node objects, not strings)
    const forceLinks: ForceLink[] = simLinks
      .filter(l => !l.isSelfLoop)
      .map(link => {
        const sourceNode = simNodes.find(n => n.id === (link.source as string));
        const targetNode = simNodes.find(n => n.id === (link.target as string));
        if (!sourceNode || !targetNode) return null;
        return {
          id: link.id,
          source: sourceNode,
          target: targetNode,
          label: link.label,
          hasError: link.hasError,
          isSelfLoop: link.isSelfLoop,
          offset: link.offset,
        };
      })
      .filter((l): l is ForceLink => l !== null);

    // Custom force to prevent edge crossings
    const edgeRepulsionForce = (alpha: number) => {
      const strength = 500 * alpha;
      
      for (let i = 0; i < forceLinks.length; i++) {
        const link1 = forceLinks[i];
        const source1 = link1.source;
        const target1 = link1.target;
        
        for (let j = i + 1; j < forceLinks.length; j++) {
          const link2 = forceLinks[j];
          const source2 = link2.source;
          const target2 = link2.target;
          
          // Skip if edges share a node
          if (source1.id === source2.id || source1.id === target2.id ||
              target1.id === source2.id || target1.id === target2.id) continue;
          
          // Calculate edge midpoints
          const mid1x = (source1.x! + target1.x!) / 2;
          const mid1y = (source1.y! + target1.y!) / 2;
          const mid2x = (source2.x! + target2.x!) / 2;
          const mid2y = (target2.y! + target2.y!) / 2;
          
          // Calculate distance between edge midpoints
          const dx = mid2x - mid1x;
          const dy = mid2y - mid1y;
          const distance = Math.sqrt(dx * dx + dy * dy);
          const minDistance = 80;
          
          if (distance < minDistance && distance > 0) {
            const force = strength * (minDistance - distance) / distance;
            const fx = dx * force;
            const fy = dy * force;
            
            // Push edges apart
            source1.x! -= fx * 0.1;
            source1.y! -= fy * 0.1;
            target1.x! -= fx * 0.1;
            target1.y! -= fy * 0.1;
            source2.x! += fx * 0.1;
            source2.y! += fy * 0.1;
            target2.x! += fx * 0.1;
            target2.y! += fy * 0.1;
          }
        }
      }
    };

    // Create force simulation with stronger forces to prevent overlap
    const simulation = d3.forceSimulation(simNodes)
      .force('link', d3.forceLink(forceLinks)
        .id((d: any) => d.id)
        .distance(300) // Increased from 250
        .strength(0.5)) // Increased from 0.4
      .force('charge', d3.forceManyBody().strength(-5000)) // Increased from -2500
      .force('center', d3.forceCenter(width / 2, height / 2))
      .force('collision', d3.forceCollide().radius(NODE_RADIUS + 100).strength(1.5)) // Increased radius and strength
      .force('x', d3.forceX(width / 2).strength(0.02)) // Reduced to let repulsion work
      .force('y', d3.forceY(height / 2).strength(0.02)) // Reduced to let repulsion work
      .force('edgeRepulsion', edgeRepulsionForce)
      .alpha(1)
      .alphaDecay(0.01) // Slower decay for more iterations
      .alphaMin(0.001); // Lower minimum to run longer

    simulationRef.current = simulation;

    // Create edge elements
    const edgeGroup = container.append('g').attr('class', 'edges');
    
    const edgePaths = edgeGroup.selectAll<SVGPathElement, ForceLink>('path')
      .data(forceLinks)
      .join('path')
      .attr('class', 'edge')
      .attr('fill', 'none')
      .attr('stroke-width', d => {
        if (d.hasError) return 2;
        if (isTaskSuccess) return 2;
        return 1.5;
      })
      .attr('stroke', d => {
        if (d.hasError) return 'var(--color-border-warning, #d97706)';
        if (isTaskSuccess) return 'var(--color-border-success, #6a9a23)';
        return 'var(--color-border, #e5e7eb)';
      })
      .attr('marker-end', d => {
        if (d.hasError) return 'url(#arrow-error)';
        if (isTaskSuccess) return 'url(#arrow-success)';
        return 'url(#arrow-default)';
      })
      .style('cursor', 'pointer')
      .on('click', function(event, d) {
        event.stopPropagation();
        onSelectEdgeId(d.id);
      });
    
    edgePathsRef.current = edgePaths;

    // Self-loop edges (need to attach node objects)
    const selfLoopLinks: ForceLink[] = simLinks
      .filter(l => l.isSelfLoop)
      .map(link => {
        const node = simNodes.find(n => n.id === (link.source as string));
        if (!node) return null;
        return {
          id: link.id,
          source: node,
          target: node,
          label: link.label,
          hasError: link.hasError,
          isSelfLoop: link.isSelfLoop,
          offset: link.offset,
        };
      })
      .filter((l): l is ForceLink => l !== null);

    const selfLoopGroup = container.append('g').attr('class', 'self-loops');
    
    const selfLoops = selfLoopGroup.selectAll<SVGPathElement, ForceLink>('path')
      .data(selfLoopLinks)
      .join('path')
      .attr('class', 'self-loop')
      .attr('fill', 'none')
      .attr('stroke-width', d => {
        if (d.hasError) return 2;
        return 1.5;
      })
      .attr('stroke', d => {
        if (d.hasError) return 'var(--color-border-warning, #d97706)';
        return 'var(--color-border, #e5e7eb)';
      })
      .attr('marker-end', d => {
        if (d.hasError) return 'url(#arrow-error)';
        return 'url(#arrow-default)';
      })
      .style('cursor', 'pointer')
      .on('click', function(event, d) {
        event.stopPropagation();
        onSelectEdgeId(d.id);
      });
    
    selfLoopsRef.current = selfLoops;

    // Self-loop labels
    const selfLoopLabelGroup = container.append('g').attr('class', 'self-loop-labels');
    
    const selfLoopLabels = selfLoopLabelGroup.selectAll<SVGGElement, ForceLink>('g')
      .data(selfLoopLinks.filter(l => l.label), (d: ForceLink) => d.id)
      .join('g')
      .attr('class', 'self-loop-label')
      .style('cursor', 'pointer')
      .on('click', function(event, d) {
        event.stopPropagation();
        onSelectEdgeId(d.id);
      });

    selfLoopLabels.append('rect')
      .attr('rx', 4)
      .attr('ry', 4)
      .attr('fill', 'var(--color-elevation-surface, #ffffff)')
      .attr('stroke', d => {
        if (d.hasError) return 'var(--color-border-warning, #d97706)';
        return 'var(--color-border, #e5e7eb)';
      })
      .attr('stroke-width', 1.5);

    selfLoopLabels.append('text')
      .attr('text-anchor', 'middle')
      .attr('dy', '0.35em')
      .attr('font-size', '10px')
      .attr('font-weight', 500)
      .attr('fill', d => 
        d.hasError 
          ? 'var(--color-text-warning, #d97706)' 
          : 'var(--color-text-subtle, #7d818a)'
      )
      .text(d => d.label);
    
    // Set initial positions for self-loop labels
    selfLoopLabels.attr('transform', d => {
      const node = d.source;
      const loopRadius = 40 + d.offset * 100;
      const y = node.y! + NODE_RADIUS;
      
      // Position label at the bottom of the loop
      return `translate(${node.x},${y + loopRadius / 2})`;
    });
    
    selfLoopLabelsRef.current = selfLoopLabels;

    // Edge labels
    const edgeLabelGroup = container.append('g').attr('class', 'edge-labels');
    
    const edgeLabels = edgeLabelGroup.selectAll<SVGGElement, ForceLink>('g')
      .data(forceLinks.filter(l => l.label), (d: ForceLink) => d.id)
      .join('g')
      .attr('class', 'edge-label')
      .style('cursor', 'pointer')
      .on('click', function(event, d) {
        event.stopPropagation();
        onSelectEdgeId(d.id);
      });

    edgeLabels.append('rect')
      .attr('rx', 4)
      .attr('ry', 4)
      .attr('fill', 'var(--color-elevation-surface, #ffffff)')
      .attr('stroke', d => {
        if (d.hasError) return 'var(--color-border-warning, #d97706)';
        if (isTaskSuccess) return 'var(--color-border-success, #6a9a23)';
        return 'var(--color-border, #e5e7eb)';
      })
      .attr('stroke-width', 1.5);

    edgeLabels.append('text')
      .attr('text-anchor', 'middle')
      .attr('dy', '0.35em')
      .attr('font-size', '10px')
      .attr('font-weight', 500)
      .attr('fill', d => 
        d.hasError 
          ? 'var(--color-text-warning, #d97706)' 
          : 'var(--color-text-subtle, #7d818a)'
      )
      .text(d => d.label);
    
    // Set initial positions for edge labels
    edgeLabels.attr('transform', d => {
      const source = d.source;
      const target = d.target;
      
      const dx = target.x! - source.x!;
      const dy = target.y! - source.y!;
      const offsetX = -dy * 0.25;
      const offsetY = dx * 0.25;
      
      const x = (source.x! + target.x!) / 2 + offsetX;
      const y = (source.y! + target.y!) / 2 + offsetY;
      
      return `translate(${x},${y})`;
    });
    
    edgeLabelsRef.current = edgeLabels;

    // Node elements
    const nodeGroup = container.append('g').attr('class', 'nodes');
    
    const nodes = nodeGroup.selectAll<SVGGElement, SimNode>('g')
      .data(simNodes)
      .join('g')
      .attr('class', 'node')
      .style('cursor', 'pointer')
      .on('click', function(event, d) {
        event.stopPropagation();
        onSelectNodeId(d.id);
      });

    nodes.append('circle')
      .attr('r', NODE_RADIUS)
      .attr('fill', d => {
        if (d.isSuccess) return 'var(--color-background-success, #ecfccb)';
        if (d.hasError) return 'var(--color-background-warning, #fef3c7)';
        return 'var(--color-elevation-surface, #ffffff)';
      })
      .attr('stroke', d => {
        if (d.isSuccess) return 'var(--color-border-success, #6a9a23)';
        if (d.hasError) return 'var(--color-border-warning, #d97706)';
        return 'var(--color-border, #e5e7eb)';
      })
      .attr('stroke-width', 2);
    
    // Set initial positions
    nodes.attr('transform', d => `translate(${d.x},${d.y})`);
    
    nodesRef.current = nodes;

    // Update positions on tick
    function ticked() {
      // Update regular edges with bezier curves
      edgePaths.attr('d', d => {
        const source = d.source;
        const target = d.target;
        
        // Calculate control point for bezier curve
        const dx = target.x! - source.x!;
        const dy = target.y! - source.y!;
        
        // Perpendicular offset for curve
        const offsetX = -dy * 0.25;
        const offsetY = dx * 0.25;
        
        const midX = (source.x! + target.x!) / 2 + offsetX;
        const midY = (source.y! + target.y!) / 2 + offsetY;
        
        // Adjust end point for arrow marker
        const angle = Math.atan2(dy, dx);
        const targetX = target.x! - Math.cos(angle) * (NODE_RADIUS + 8);
        const targetY = target.y! - Math.sin(angle) * (NODE_RADIUS + 8);
        
        return `M ${source.x},${source.y} Q ${midX},${midY} ${targetX},${targetY}`;
      });

      // Update self-loops (curve outward/downward)
      selfLoops.attr('d', d => {
        const node = d.source;
        const loopRadius = 40 + d.offset * 100;
        
        const startX = node.x! - NODE_RADIUS;
        const endX = node.x! + NODE_RADIUS;
        const y = node.y! + NODE_RADIUS; // Start from bottom of node
        const centerX = node.x!;
        
        // Curve outward (downward) instead of inward (upward)
        return `M ${startX},${y} Q ${centerX},${y + loopRadius} ${endX},${y}`;
      });

      // Update self-loop labels
      if (selfLoopLabelsRef.current) {
        selfLoopLabelsRef.current.attr('transform', d => {
          const node = d.source;
          const loopRadius = 40 + d.offset * 100;
          const y = node.y! + NODE_RADIUS;
          
          // Position label at the bottom of the loop
          return `translate(${node.x},${y + loopRadius / 2})`;
        });

        // Update self-loop label backgrounds to fit text
        selfLoopLabelsRef.current.each(function() {
          const label = d3.select(this);
          const text = label.select('text').node() as SVGTextElement;
          const bbox = text?.getBBox();
          if (bbox) {
            label.select('rect')
              .attr('x', bbox.x - 4)
              .attr('y', bbox.y - 2)
              .attr('width', bbox.width + 8)
              .attr('height', bbox.height + 4);
          }
        });
      }

      // Update edge labels
      if (edgeLabelsRef.current) {
        edgeLabelsRef.current.attr('transform', d => {
          const source = d.source;
          const target = d.target;
          
          const dx = target.x! - source.x!;
          const dy = target.y! - source.y!;
          const offsetX = -dy * 0.25;
          const offsetY = dx * 0.25;
          
          const x = (source.x! + target.x!) / 2 + offsetX;
          const y = (source.y! + target.y!) / 2 + offsetY;
          
          return `translate(${x},${y})`;
        });

        // Update label backgrounds to fit text
        edgeLabelsRef.current.each(function() {
          const label = d3.select(this);
          const text = label.select('text').node() as SVGTextElement;
          const bbox = text?.getBBox();
          if (bbox) {
            label.select('rect')
              .attr('x', bbox.x - 4)
              .attr('y', bbox.y - 2)
              .attr('width', bbox.width + 8)
              .attr('height', bbox.height + 4);
          }
        });
      }

      // Update nodes
      nodes.attr('transform', d => `translate(${d.x},${d.y})`);
    }

    simulation.on('tick', ticked);
    
    // Call ticked once to render initial positions
    ticked();
    
    // Ensure simulation runs
    if (simulation.alpha() < simulation.alphaMin()) {
      simulation.alpha(1).restart();
    }

    // Zoom to fit after simulation settles
    simulation.on('end', () => {
      const bounds = container.node()?.getBBox();
      if (bounds) {
        const fullWidth = bounds.width;
        const fullHeight = bounds.height;
        const midX = bounds.x + fullWidth / 2;
        const midY = bounds.y + fullHeight / 2;
        
        const scale = 0.8 / Math.max(fullWidth / width, fullHeight / height);
        const clampedScale = Math.min(Math.max(scale, 0.1), 1.2);
        
        const translate = [
          width / 2 - clampedScale * midX,
          height / 2 - clampedScale * midY
        ];
        
        // Use zoom transform for proper zoom/pan behavior
        svg.transition()
          .duration(750)
          .call(zoom.transform as any, d3.zoomIdentity
            .translate(translate[0], translate[1])
            .scale(clampedScale));
      }
    });

    return () => {
      simulation.stop();
    };
  }, [graph, onSelectNodeId, onSelectEdgeId]);

  // Update selection styles without re-rendering
  useEffect(() => {
    if (!edgePathsRef.current || !selfLoopsRef.current || !edgeLabelsRef.current || !nodesRef.current) return;

    const isTaskSuccess = isTaskSuccessRef.current;

    // Update edge paths
    edgePathsRef.current
      .attr('stroke-width', d => {
        if (d.id === selectedEdgeId) return 3;
        if (d.hasError) return 2;
        if (isTaskSuccess) return 2;
        return 1.5;
      })
      .attr('stroke', d => {
        if (d.hasError) return 'var(--color-border-warning, #d97706)';
        if (d.id === selectedEdgeId) return 'var(--color-border-bold, #7d818a)';
        if (isTaskSuccess) return 'var(--color-border-success, #6a9a23)';
        return 'var(--color-border, #e5e7eb)';
      })
      .attr('marker-end', d => {
        if (d.hasError) return 'url(#arrow-error)';
        if (d.id === selectedEdgeId) return 'url(#arrow-selected)';
        if (isTaskSuccess) return 'url(#arrow-success)';
        return 'url(#arrow-default)';
      });

    // Update self-loops
    selfLoopsRef.current
      .attr('stroke-width', d => {
        if (d.id === selectedEdgeId) return 3;
        if (d.hasError) return 2;
        return 1.5;
      })
      .attr('stroke', d => {
        if (d.hasError) return 'var(--color-border-warning, #d97706)';
        if (d.id === selectedEdgeId) return 'var(--color-border-bold, #7d818a)';
        return 'var(--color-border, #e5e7eb)';
      })
      .attr('marker-end', d => {
        if (d.hasError) return 'url(#arrow-error)';
        if (d.id === selectedEdgeId) return 'url(#arrow-selected)';
        return 'url(#arrow-default)';
      });

    // Update self-loop label backgrounds
    if (selfLoopLabelsRef.current) {
      selfLoopLabelsRef.current.each(function(d) {
        const label = d3.select(this);
        const linkData = d as ForceLink;
        label.select('rect')
          .attr('stroke', () => {
            if (linkData.hasError) return 'var(--color-border-warning, #d97706)';
            if (linkData.id === selectedEdgeId) return 'var(--color-border-bold, #7d818a)';
            return 'var(--color-border, #e5e7eb)';
          })
          .attr('stroke-width', () => {
            if (linkData.hasError) return 1.5;
            if (linkData.id === selectedEdgeId) return 2;
            return 1.5;
          });
      });
    }

    // Update edge label backgrounds
    edgeLabelsRef.current.each(function(d) {
      const label = d3.select(this);
      const linkData = d as SimLink;
      label.select('rect')
        .attr('stroke', () => {
          if (linkData.hasError) return 'var(--color-border-warning, #d97706)';
          if (linkData.id === selectedEdgeId) return 'var(--color-border-bold, #7d818a)';
          if (isTaskSuccess) return 'var(--color-border-success, #6a9a23)';
          return 'var(--color-border, #e5e7eb)';
        })
        .attr('stroke-width', () => {
          if (linkData.hasError) return 1.5;
          if (linkData.id === selectedEdgeId) return 2;
          return 1.5;
        });
    });

    // Update nodes
    nodesRef.current.each(function(d) {
      const node = d3.select(this);
      const nodeData = d as SimNode;
      node.select('circle')
        .attr('stroke', () => {
          if (nodeData.id === selectedNodeId) return 'var(--color-border-bold, #7d818a)';
          if (nodeData.isSuccess) return 'var(--color-border-success, #6a9a23)';
          if (nodeData.hasError) return 'var(--color-border-warning, #d97706)';
          return 'var(--color-border, #e5e7eb)';
        })
        .attr('stroke-width', () => nodeData.id === selectedNodeId ? 3 : 2);
    });
  }, [selectedNodeId, selectedEdgeId]);

  if (!graph.graph.nodes.length) {
    return (
      <div className='text-sm text-text-disabled'>No nodes to render.</div>
    );
  }

  return (
    <div className='w-full h-full rounded-lg border border-elevation-surface-overlay overflow-hidden bg-elevation-surface-sunken'>
      <svg
        ref={svgRef}
        className='w-full h-full'
        style={{ background: 'var(--color-elevation-surface-sunken, #f9fafb)' }}
      />
    </div>
  );
};

export default TacticGraphView;
