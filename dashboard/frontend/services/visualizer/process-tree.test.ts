import {
  analyzeProcessNodes,
  createEnhancedSpans,
  rebuildProcessHierarchy,
  type EnhancedSpan,
  type ProcessNode,
} from './process-tree';
import type { VisualizerSpanLite } from '@/services/dataservice';

describe('process-tree', () => {
  describe('analyzeProcessNodes', () => {
    it('should identify root process nodes', () => {
      const spans: VisualizerSpanLite[] = [
        {
          trace_id: 'trace1',
          span_id: 'span1',
          name: 'strategy_agent/process',
          service_name: 'service1',
          attributes: {
            parent: '0',
            id: 'process1',
          },
        },
      ];

      const result = analyzeProcessNodes(spans);
      const node = result.get('span1');

      expect(node).toBeDefined();
      expect(node?.isRoot).toBe(true);
      expect(node?.isError).toBe(false);
      expect(node?.isSuccess).toBe(false);
      expect(node?.processParent).toBe('0');
      expect(node?.processId).toBe('process1');
    });

    it('should identify error process nodes', () => {
      const spans: VisualizerSpanLite[] = [
        {
          trace_id: 'trace1',
          span_id: 'span1',
          name: 'strategy_agent/process',
          service_name: 'service1',
          attributes: {
            parent: 'process1',
            id: undefined,
          },
        },
      ];

      const result = analyzeProcessNodes(spans);
      const node = result.get('span1');

      expect(node).toBeDefined();
      expect(node?.isRoot).toBe(false);
      expect(node?.isError).toBe(true);
      expect(node?.isSuccess).toBe(false);
      expect(node?.processParent).toBe('process1');
      expect(node?.processId).toBeNull();
    });

    it('should identify success process nodes', () => {
      const spans: VisualizerSpanLite[] = [
        {
          trace_id: 'trace1',
          span_id: 'span1',
          name: 'strategy_agent/process',
          service_name: 'service1',
          attributes: {
            parent: 'process1',
            id: 'process2',
          },
        },
      ];

      const result = analyzeProcessNodes(spans);
      const node = result.get('span1');

      expect(node).toBeDefined();
      expect(node?.isRoot).toBe(false);
      expect(node?.isError).toBe(false);
      expect(node?.isSuccess).toBe(true);
      expect(node?.processParent).toBe('process1');
      expect(node?.processId).toBe('process2');
    });

    it('should identify intermediate process nodes', () => {
      const spans: VisualizerSpanLite[] = [
        {
          trace_id: 'trace1',
          span_id: 'span1',
          name: 'strategy_agent/process',
          service_name: 'service1',
          attributes: {
            parent: 'process1',
            id: 'process2',
          },
        },
        {
          trace_id: 'trace1',
          span_id: 'span2',
          name: 'strategy_agent/process',
          service_name: 'service1',
          attributes: {
            parent: 'process2',
            id: 'process3',
          },
        },
      ];

      const result = analyzeProcessNodes(spans);
      const node = result.get('span1');

      expect(node).toBeDefined();
      expect(node?.isRoot).toBe(false);
      expect(node?.isError).toBe(false);
      expect(node?.isSuccess).toBe(false); // Has children, so not success
    });

    it('should ignore non-strategy_agent/process spans', () => {
      const spans: VisualizerSpanLite[] = [
        {
          trace_id: 'trace1',
          span_id: 'span1',
          name: 'other/span',
          service_name: 'service1',
          attributes: {
            parent: '0',
            id: 'process1',
          },
        },
      ];

      const result = analyzeProcessNodes(spans);
      expect(result.size).toBe(0);
    });

    it('should handle spans without attributes', () => {
      const spans: VisualizerSpanLite[] = [
        {
          trace_id: 'trace1',
          span_id: 'span1',
          name: 'strategy_agent/process',
          service_name: 'service1',
        },
      ];

      const result = analyzeProcessNodes(spans);
      const node = result.get('span1');

      expect(node).toBeDefined();
      expect(node?.isRoot).toBe(false);
      expect(node?.isError).toBe(false);
      expect(node?.isSuccess).toBe(false);
      expect(node?.processParent).toBeNull();
      expect(node?.processId).toBeNull();
    });

    it('should handle complex process hierarchies', () => {
      const spans: VisualizerSpanLite[] = [
        {
          trace_id: 'trace1',
          span_id: 'root',
          name: 'strategy_agent/process',
          service_name: 'service1',
          attributes: { parent: '0', id: 'p1' },
        },
        {
          trace_id: 'trace1',
          span_id: 'intermediate',
          name: 'strategy_agent/process',
          service_name: 'service1',
          attributes: { parent: 'p1', id: 'p2' },
        },
        {
          trace_id: 'trace1',
          span_id: 'success',
          name: 'strategy_agent/process',
          service_name: 'service1',
          attributes: { parent: 'p2', id: 'p3' },
        },
        {
          trace_id: 'trace1',
          span_id: 'error',
          name: 'strategy_agent/process',
          service_name: 'service1',
          attributes: { parent: 'p1', id: undefined },
        },
      ];

      const result = analyzeProcessNodes(spans);

      expect(result.get('root')?.isRoot).toBe(true);
      expect(result.get('intermediate')?.isSuccess).toBe(false);
      expect(result.get('success')?.isSuccess).toBe(true);
      expect(result.get('error')?.isError).toBe(true);
    });
  });

  describe('createEnhancedSpans', () => {
    it('should enhance process nodes with correct state', () => {
      const spans: VisualizerSpanLite[] = [
        {
          trace_id: 'trace1',
          span_id: 'span1',
          name: 'strategy_agent/process',
          service_name: 'service1',
          attributes: { parent: '0', id: 'process1' },
        },
      ];

      const processNodes = analyzeProcessNodes(spans);
      const enhanced = createEnhancedSpans(spans, processNodes);

      expect(enhanced).toHaveLength(1);
      expect(enhanced[0].isProcessNode).toBe(true);
      expect(enhanced[0].processState).toBe('root');
    });

    it('should create virtual error nodes for error process nodes', () => {
      const spans: VisualizerSpanLite[] = [
        {
          trace_id: 'trace1',
          span_id: 'span1',
          name: 'strategy_agent/process',
          service_name: 'service1',
          end_time_unix_nano: '1000000',
          attributes: { parent: 'process1', id: undefined },
        },
      ];

      const processNodes = analyzeProcessNodes(spans);
      const enhanced = createEnhancedSpans(spans, processNodes);

      expect(enhanced).toHaveLength(2);
      expect(enhanced[0].isProcessNode).toBe(true);
      expect(enhanced[0].processState).toBe('error');

      const virtualNode = enhanced[1];
      expect(virtualNode.virtualErrorNode).toBe(true);
      expect(virtualNode.span_id).toBe('span1_error');
      expect(virtualNode.parent_span_id).toBe('span1');
      expect(virtualNode.name).toBe('Error');
      expect(virtualNode.originalSpanId).toBe('span1');
      expect(virtualNode.attributes?.error).toBe(true);
    });

    it('should keep regular spans unchanged', () => {
      const spans: VisualizerSpanLite[] = [
        {
          trace_id: 'trace1',
          span_id: 'span1',
          name: 'regular/span',
          service_name: 'service1',
        },
      ];

      const processNodes = analyzeProcessNodes(spans);
      const enhanced = createEnhancedSpans(spans, processNodes);

      expect(enhanced).toHaveLength(1);
      expect(enhanced[0].isProcessNode).toBeUndefined();
      expect(enhanced[0].processState).toBeUndefined();
      expect(enhanced[0].span_id).toBe('span1');
    });

    it('should handle mixed spans correctly', () => {
      const spans: VisualizerSpanLite[] = [
        {
          trace_id: 'trace1',
          span_id: 'regular1',
          name: 'regular/span',
          service_name: 'service1',
        },
        {
          trace_id: 'trace1',
          span_id: 'process1',
          name: 'strategy_agent/process',
          service_name: 'service1',
          attributes: { parent: '0', id: 'p1' },
        },
        {
          trace_id: 'trace1',
          span_id: 'error1',
          name: 'strategy_agent/process',
          service_name: 'service1',
          end_time_unix_nano: '1000000',
          attributes: { parent: 'p1', id: undefined },
        },
      ];

      const processNodes = analyzeProcessNodes(spans);
      const enhanced = createEnhancedSpans(spans, processNodes);

      expect(enhanced).toHaveLength(4); // 3 original + 1 virtual error
      expect(enhanced.find(s => s.span_id === 'regular1')?.isProcessNode).toBeUndefined();
      expect(enhanced.find(s => s.span_id === 'process1')?.isProcessNode).toBe(true);
      expect(enhanced.find(s => s.span_id === 'error1_error')?.virtualErrorNode).toBe(true);
    });
  });

  describe('rebuildProcessHierarchy', () => {
    it('should keep root nodes unchanged', () => {
      const spans: EnhancedSpan[] = [
        {
          trace_id: 'trace1',
          span_id: 'root',
          parent_span_id: 'strategy_agent',
          name: 'strategy_agent/process',
          service_name: 'service1',
          isProcessNode: true,
          processState: 'root',
          attributes: { parent: '0', id: 'p1' },
        },
      ];

      const processNodes = analyzeProcessNodes(
        spans as VisualizerSpanLite[]
      );
      const rebuilt = rebuildProcessHierarchy(spans, processNodes);

      expect(rebuilt[0].parent_span_id).toBe('strategy_agent');
    });

    it('should update parent_span_id for non-root process nodes', () => {
      const spans: EnhancedSpan[] = [
        {
          trace_id: 'trace1',
          span_id: 'parent',
          name: 'strategy_agent/process',
          service_name: 'service1',
          isProcessNode: true,
          processState: 'root',
          attributes: { parent: '0', id: 'p1' },
        },
        {
          trace_id: 'trace1',
          span_id: 'child',
          parent_span_id: 'original_parent',
          name: 'strategy_agent/process',
          service_name: 'service1',
          isProcessNode: true,
          processState: 'intermediate',
          attributes: { parent: 'p1', id: 'p2' },
        },
      ];

      const processNodes = analyzeProcessNodes(
        spans as VisualizerSpanLite[]
      );
      const rebuilt = rebuildProcessHierarchy(spans, processNodes);

      const childNode = rebuilt.find(s => s.span_id === 'child');
      expect(childNode?.parent_span_id).toBe('parent');
    });

    it('should keep non-process nodes unchanged', () => {
      const spans: EnhancedSpan[] = [
        {
          trace_id: 'trace1',
          span_id: 'regular',
          parent_span_id: 'original_parent',
          name: 'regular/span',
          service_name: 'service1',
        },
      ];

      const processNodes = new Map<string, ProcessNode>();
      const rebuilt = rebuildProcessHierarchy(spans, processNodes);

      expect(rebuilt[0].parent_span_id).toBe('original_parent');
    });

    it('should handle nodes without matching parent', () => {
      const spans: EnhancedSpan[] = [
        {
          trace_id: 'trace1',
          span_id: 'orphan',
          parent_span_id: 'original_parent',
          name: 'strategy_agent/process',
          service_name: 'service1',
          isProcessNode: true,
          processState: 'intermediate',
          attributes: { parent: 'nonexistent', id: 'p1' },
        },
      ];

      const processNodes = analyzeProcessNodes(
        spans as VisualizerSpanLite[]
      );
      const rebuilt = rebuildProcessHierarchy(spans, processNodes);

      expect(rebuilt[0].parent_span_id).toBe('original_parent');
    });

    it('should rebuild complex hierarchy correctly', () => {
      const spans: EnhancedSpan[] = [
        {
          trace_id: 'trace1',
          span_id: 'root',
          name: 'strategy_agent/process',
          service_name: 'service1',
          isProcessNode: true,
          processState: 'root',
          attributes: { parent: '0', id: 'p1' },
        },
        {
          trace_id: 'trace1',
          span_id: 'level1',
          name: 'strategy_agent/process',
          service_name: 'service1',
          isProcessNode: true,
          processState: 'intermediate',
          attributes: { parent: 'p1', id: 'p2' },
        },
        {
          trace_id: 'trace1',
          span_id: 'level2',
          name: 'strategy_agent/process',
          service_name: 'service1',
          isProcessNode: true,
          processState: 'success',
          attributes: { parent: 'p2', id: 'p3' },
        },
      ];

      const processNodes = analyzeProcessNodes(
        spans as VisualizerSpanLite[]
      );
      const rebuilt = rebuildProcessHierarchy(spans, processNodes);

      expect(rebuilt.find(s => s.span_id === 'level1')?.parent_span_id).toBe('root');
      expect(rebuilt.find(s => s.span_id === 'level2')?.parent_span_id).toBe('level1');
    });
  });
});
