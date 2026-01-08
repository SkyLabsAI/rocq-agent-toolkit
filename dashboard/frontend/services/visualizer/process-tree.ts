import type { VisualizerSpanLite } from '@/services/dataservice';

export interface ProcessNode {
  span: VisualizerSpanLite;
  isRoot: boolean;
  isError: boolean;
  isSuccess: boolean;
  processParent: string | null; // The 'parent' attribute value
  processId: string | null; // The 'id' attribute value
  virtualErrorChild?: boolean; // Flag for virtual error nodes
}

export interface EnhancedSpan extends VisualizerSpanLite {
  isProcessNode?: boolean;
  processState?: 'root' | 'intermediate' | 'error' | 'success';
  virtualErrorNode?: boolean;
  originalSpanId?: string; // For virtual nodes, reference to parent
}

/**
 * Analyzes strategy_agent/process spans and determines their state
 */
export function analyzeProcessNodes(
  spans: VisualizerSpanLite[]
): Map<string, ProcessNode> {
  const processNodes = new Map<string, ProcessNode>();

  // First pass: identify all strategy_agent/process nodes
  const strategyProcessSpans = spans.filter(
    s => s.name === 'strategy_agent/process'
  );

  // Build a map of process IDs to spans
  const processIdToSpans = new Map<string, VisualizerSpanLite[]>();
  strategyProcessSpans.forEach(span => {
    const attrs = span.attributes || {};
    const processId = attrs.id as string | undefined;
    if (processId) {
      if (!processIdToSpans.has(processId)) {
        processIdToSpans.set(processId, []);
      }
      processIdToSpans.get(processId)!.push(span);
    }
  });

  // Second pass: analyze each process node
  strategyProcessSpans.forEach(span => {
    const attrs = span.attributes || {};
    const parent = attrs.parent as string | undefined;
    const id = attrs.id as string | undefined;

    const isRoot = parent === '0' && id != null;
    const isError = parent != null && id == null;

    // Check if this node has children (other nodes reference its id as parent)
    let hasChildren = false;
    if (id != null) {
      hasChildren = strategyProcessSpans.some(
        s => s.attributes?.parent === id && s.span_id !== span.span_id
      );
    }

    const isSuccess = id != null && !hasChildren && !isRoot;

    processNodes.set(span.span_id, {
      span,
      isRoot,
      isError,
      isSuccess,
      processParent: parent || null,
      processId: id || null,
    });
  });

  return processNodes;
}

/**
 * Creates enhanced spans with virtual error nodes
 */
export function createEnhancedSpans(
  spans: VisualizerSpanLite[],
  processNodes: Map<string, ProcessNode>
): EnhancedSpan[] {
  const enhanced: EnhancedSpan[] = [];

  spans.forEach(span => {
    const processNode = processNodes.get(span.span_id);

    if (processNode) {
      // This is a strategy_agent/process node
      const enhancedSpan: EnhancedSpan = {
        ...span,
        isProcessNode: true,
        processState: processNode.isRoot
          ? 'root'
          : processNode.isError
            ? 'error'
            : processNode.isSuccess
              ? 'success'
              : 'intermediate',
      };
      enhanced.push(enhancedSpan);

      // Add virtual error child if this is an error node
      if (processNode.isError) {
        const virtualErrorSpan: EnhancedSpan = {
          trace_id: span.trace_id,
          span_id: `${span.span_id}_error`,
          parent_span_id: span.span_id,
          name: 'Error',
          service_name: span.service_name,
          start_time_unix_nano: span.end_time_unix_nano,
          end_time_unix_nano: span.end_time_unix_nano,
          attributes: {
            error: true,
            message: 'Process terminated without completion',
          },
          virtualErrorNode: true,
          originalSpanId: span.span_id,
        };
        enhanced.push(virtualErrorSpan);
      }
    } else {
      // Regular span, keep as is
      enhanced.push({ ...span });
    }
  });

  return enhanced;
}

/**
 * Rebuilds parent-child relationships for process nodes based on parent/id attributes
 */
export function rebuildProcessHierarchy(
  spans: EnhancedSpan[],
  processNodes: Map<string, ProcessNode>
): EnhancedSpan[] {
  const result = spans.map(span => {
    // Only modify strategy_agent/process nodes
    if (!span.isProcessNode) {
      return span;
    }

    const processNode = processNodes.get(span.span_id);
    if (!processNode) {
      return span;
    }

    // Find the actual parent span based on the 'parent' attribute
    const parentAttrValue = processNode.processParent;
    if (parentAttrValue === '0') {
      // Root node - keep its original parent_span_id (points to strategy_agent)
      return span;
    }

    // Find the span that has this parent value as its 'id'
    const parentSpan = Array.from(processNodes.values()).find(
      pn => pn.processId === parentAttrValue
    );

    if (parentSpan) {
      // Update parent_span_id to point to the correct parent
      return {
        ...span,
        parent_span_id: parentSpan.span.span_id,
      };
    }

    return span;
  });

  return result;
}
