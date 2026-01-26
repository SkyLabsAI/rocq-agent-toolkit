'use client';

import { type ReactNode, useEffect, useMemo, useState } from 'react';

import CodeViewer from '@/components/base/codeViewer';
import { StatusBadge } from '@/components/base/statusBadge';
import Modal from '@/components/base/ui/modal';
import FlamegraphView from '@/components/visualizer/flamegraph-view';
import SpanGraphView from '@/components/visualizer/span-graph-view';
import TacticGraphView from '@/components/visualizer/tactic-graph-view';
import {
  getTacticGraph,
  type TacticGraphResponse,
} from '@/services/dataservice';
import {
  getLogsBySpan,
  getParsedSpansForTrace,
  getTraceIdsForRun,
  type VisualizerSpanLite,
} from '@/services/visualizer';
import {
  analyzeProcessNodes,
  createEnhancedSpans,
  type EnhancedSpan,
  rebuildProcessHierarchy,
} from '@/services/visualizer/process-tree';

type Props = {
  isOpen: boolean;
  onClose: () => void;
  runId: string;
  runTimestampUtc: string;
  initialTraceId?: string;
  taskId?: number;
};

const VisualizerModal = ({
  isOpen,
  onClose,
  runId,
  runTimestampUtc,
  initialTraceId,
  taskId,
}: Props) => {
  const [activeTab, setActiveTab] = useState<
    'traces' | 'flamegraph' | 'tactic'
  >('traces');
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const [traceIds, setTraceIds] = useState<string[]>([]);
  const [selectedTraceId, setSelectedTraceId] = useState<string>('');

  const [spans, setSpans] = useState<VisualizerSpanLite[]>([]);
  const [enhancedSpans, setEnhancedSpans] = useState<EnhancedSpan[]>([]);
  const [selectedSpan, setSelectedSpan] = useState<EnhancedSpan | null>(null);
  const [logs, setLogs] = useState<Record<string, unknown> | null>(null);
  const [logsLoading, setLogsLoading] = useState(false);

  // New states for collapsible nodes and depth control
  const [collapsedNodes, setCollapsedNodes] = useState<Set<string>>(new Set());
  const [maxDepth, setMaxDepth] = useState<number | null>(null);

  // Tactic graph states
  const [tacticGraph, setTacticGraph] = useState<TacticGraphResponse | null>(
    null
  );
  const [tacticGraphLoading, setTacticGraphLoading] = useState(false);
  const [tacticGraphError, setTacticGraphError] = useState<string | null>(null);
  const [selectedTacticNode, setSelectedTacticNode] = useState<string | null>(
    null
  );
  const [selectedTacticEdge, setSelectedTacticEdge] = useState<string | null>(
    null
  );

  const runTsMs = useMemo(
    () => normalizeRunTimestampMs(runTimestampUtc),
    [runTimestampUtc]
  );

  const range = useMemo(() => {
    const now = Date.now();
    const base = runTsMs ?? now;
    const startMs = base - 30 * 60_000;
    const endMs = Math.min(now, base + 2 * 60 * 60_000);
    return { startMs, endMs };
  }, [runTsMs]);

  // Reset state on open / run changes.
  useEffect(() => {
    if (!isOpen) return;
    setError(null);
    setTraceIds([]);
    setSelectedTraceId('');
    setSpans([]);
    setSelectedSpan(null);
    setLogs(null);
    setCollapsedNodes(new Set());
    setMaxDepth(null);
    setTacticGraph(null);
    setTacticGraphError(null);
    setSelectedTacticNode(null);
    // Default to traces tab if no taskId, otherwise default to tactic tab
    setActiveTab(taskId ? 'tactic' : 'traces');
  }, [isOpen, runId, taskId]);

  // Auto-load trace ids for this run.
  useEffect(() => {
    if (!isOpen) return;
    let cancelled = false;

    async function load() {
      setLoading(true);
      setError(null);
      try {
        // If initialTraceId is provided, use it directly
        if (initialTraceId) {
          setTraceIds([initialTraceId]);
          setSelectedTraceId(initialTraceId);
          if (!cancelled) setLoading(false);
          return;
        }

        // Otherwise, fetch trace IDs for the run
        const res = await getTraceIdsForRun(runId, {
          startMs: range.startMs,
          endMs: range.endMs,
          limit: 50,
        });
        if (cancelled) return;
        setTraceIds(res.trace_ids);
        setSelectedTraceId(res.trace_ids[0] ?? '');
        if (!res.trace_ids.length) {
          setError('No traces found for this run in the selected time window.');
        }
      } catch (e) {
        if (cancelled) return;
        setError(e instanceof Error ? e.message : `${e}`);
      } finally {
        if (!cancelled) setLoading(false);
      }
    }

    load();
    return () => {
      cancelled = true;
    };
  }, [isOpen, runId, range.startMs, range.endMs, initialTraceId]);

  // Fetch spans for selected trace id.
  useEffect(() => {
    if (!isOpen) return;
    if (!selectedTraceId) return;
    let cancelled = false;

    async function loadSpans() {
      setLoading(true);
      setError(null);
      setSpans([]);
      setEnhancedSpans([]);
      setSelectedSpan(null);
      setLogs(null);
      try {
        const res = await getParsedSpansForTrace(selectedTraceId);
        if (cancelled) return;
        const rawSpans = res.spans ?? [];
        setSpans(rawSpans);

        // Analyze and enhance process nodes
        const processNodes = analyzeProcessNodes(rawSpans);
        let enhanced = createEnhancedSpans(rawSpans, processNodes);
        enhanced = rebuildProcessHierarchy(enhanced, processNodes);
        setEnhancedSpans(enhanced);
      } catch (e) {
        if (cancelled) return;
        setError(e instanceof Error ? e.message : `${e}`);
      } finally {
        if (!cancelled) setLoading(false);
      }
    }

    loadSpans();
    return () => {
      cancelled = true;
    };
  }, [isOpen, selectedTraceId]);

  // Fetch logs when span is selected.
  useEffect(() => {
    if (!isOpen) return;
    const span = selectedSpan;
    if (!span) return;
    let cancelled = false;

    async function loadLogs(spanNonNull: NonNullable<typeof span>) {
      setLogsLoading(true);
      try {
        // Skip virtual error nodes - they don't have real logs
        if (spanNonNull.virtualErrorNode) {
          setLogs({
            message:
              'This is a virtual error node indicating incomplete process',
            note: 'No logs available for virtual nodes',
          });
          setLogsLoading(false);
          return;
        }

        const data = await getLogsBySpan({
          service: spanNonNull.service_name,
          traceId: spanNonNull.trace_id,
          spanId: spanNonNull.span_id,
          startMs: range.startMs,
          endMs: range.endMs,
          limit: 200,
          direction: 'backward',
        });
        if (cancelled) return;
        setLogs(data);
      } catch (e) {
        if (cancelled) return;
        setLogs({ error: e instanceof Error ? e.message : `${e}` });
      } finally {
        if (!cancelled) setLogsLoading(false);
      }
    }

    loadLogs(span);
    return () => {
      cancelled = true;
    };
  }, [isOpen, selectedSpan, range.startMs, range.endMs]);

  const spansById = useMemo(
    () => new Map(enhancedSpans.map(s => [s.span_id, s] as const)),
    [enhancedSpans]
  );

  const successPathNodes = useMemo(() => {
    const out = new Set<string>();
    for (const s of enhancedSpans) {
      const raw = s.attributes?.['search.path'];
      if (!raw) continue;
      const parsed = parsePath(raw);
      if (!parsed) continue;
      for (const n of parsed) out.add(n);
    }
    return out;
  }, [enhancedSpans]);

  // Handler to toggle node collapse
  const toggleNodeCollapse = (spanId: string) => {
    setCollapsedNodes(prev => {
      const newSet = new Set(prev);
      const isCurrentlyCollapsed = newSet.has(spanId);

      if (isCurrentlyCollapsed) {
        // Expanding: remove from collapsed set
        newSet.delete(spanId);

        // Auto-collapse direct children (so they appear but are collapsed)
        const directChildren = enhancedSpans
          .filter(s => s.parent_span_id === spanId)
          .map(s => s.span_id);

        for (const childId of directChildren) {
          newSet.add(childId);
        }
      } else {
        // Collapsing: add to collapsed set
        newSet.add(spanId);
      }

      return newSet;
    });
  };

  // Handler for depth control
  const handleDepthChange = (depth: number | null) => {
    setMaxDepth(depth);

    if (depth === null) {
      // "All" selected - expand everything
      setCollapsedNodes(new Set());
    } else {
      // Reset and rebuild tree to specified depth
      const newCollapsed = new Set<string>();
      const nodeDepths = calculateNodeDepths(spans);

      for (const [spanId, nodeDepth] of nodeDepths.entries()) {
        // Collapse all nodes AT the max depth (they show but children are hidden)
        // Also collapse all nodes BEYOND the max depth (but they'll be hidden anyway)
        if (nodeDepth >= depth) {
          newCollapsed.add(spanId);
        }
        // Nodes with depth < maxDepth are expanded (not in the set)
      }

      setCollapsedNodes(newCollapsed);
    }
  };

  // Calculate depth for each node
  const calculateNodeDepths = (
    spanList: VisualizerSpanLite[]
  ): Map<string, number> => {
    const depths = new Map<string, number>();
    const spanMap = new Map(spanList.map(s => [s.span_id, s]));

    const getDepth = (spanId: string, visited = new Set<string>()): number => {
      if (depths.has(spanId)) return depths.get(spanId)!;
      if (visited.has(spanId)) return 0; // Circular reference protection

      visited.add(spanId);
      const span = spanMap.get(spanId);
      if (!span || !span.parent_span_id) {
        depths.set(spanId, 0);
        return 0;
      }

      const parentDepth = getDepth(span.parent_span_id, visited);
      const depth = parentDepth + 1;
      depths.set(spanId, depth);
      return depth;
    };

    for (const span of spanList) {
      getDepth(span.span_id);
    }

    return depths;
  };

  const maxPossibleDepth = useMemo(() => {
    const depths = calculateNodeDepths(enhancedSpans);
    return depths.size > 0 ? Math.max(...Array.from(depths.values())) : 0;
  }, [enhancedSpans]);

  // Fetch tactic graph when tactic tab is active and taskId is available
  useEffect(() => {
    if (!isOpen) return;
    if (activeTab !== 'tactic') return;
    if (!taskId) return;
    let cancelled = false;

    async function loadTacticGraph() {
      if (taskId === undefined) return;
      setTacticGraphLoading(true);
      setTacticGraphError(null);
      try {
        const graph = await getTacticGraph(runId, taskId);
        if (cancelled) return;
        setTacticGraph(graph);
      } catch (e) {
        if (cancelled) return;
        setTacticGraphError(
          e instanceof Error ? e.message : 'Failed to fetch tactic graph'
        );
      } finally {
        if (!cancelled) setTacticGraphLoading(false);
      }
    }

    loadTacticGraph();
    return () => {
      cancelled = true;
    };
  }, [isOpen, activeTab, runId, taskId]);

  return (
    <Modal
      isOpen={isOpen}
      onClose={onClose}
      title={`Visualizer - ${runId}`}
      size='full'
    >
      {/* Tabs */}
      <div className='flex gap-2 mb-4 border-b border-elevation-surface-overlay'>
        <button
          onClick={() => setActiveTab('traces')}
          className={`px-4 py-2 text-sm font-medium border-b-2 transition-colors ${
            activeTab === 'traces'
              ? 'border-text-information text-text'
              : 'border-transparent text-text-disabled hover:text-text'
          }`}
        >
          Traces
        </button>
        <button
          onClick={() => setActiveTab('flamegraph')}
          className={`px-4 py-2 text-sm font-medium border-b-2 transition-colors ${
            activeTab === 'flamegraph'
              ? 'border-text-information text-text'
              : 'border-transparent text-text-disabled hover:text-text'
          }`}
        >
          Flamegraph
        </button>
        {taskId && (
          <button
            onClick={() => setActiveTab('tactic')}
            className={`px-4 py-2 text-sm font-medium border-b-2 transition-colors ${
              activeTab === 'tactic'
                ? 'border-text-information text-text'
                : 'border-transparent text-text-disabled hover:text-text'
            }`}
          >
            Tactic Graph
          </button>
        )}
      </div>

      <div className='flex gap-4 h-[80vh]' data-testid='visualizer-modal'>
        {activeTab === 'traces' ? (
          <TracesVisualization
            traceIds={traceIds}
            selectedTraceId={selectedTraceId}
            setSelectedTraceId={setSelectedTraceId}
            spans={spans}
            enhancedSpans={enhancedSpans}
            selectedSpan={selectedSpan}
            setSelectedSpan={setSelectedSpan}
            logs={logs}
            logsLoading={logsLoading}
            collapsedNodes={collapsedNodes}
            maxDepth={maxDepth}
            maxPossibleDepth={maxPossibleDepth}
            loading={loading}
            error={error}
            successPathNodes={successPathNodes}
            spansById={spansById}
            onToggleCollapse={toggleNodeCollapse}
            onDepthChange={handleDepthChange}
          />
        ) : activeTab === 'flamegraph' ? (
          <FlamegraphVisualization
            traceIds={traceIds}
            selectedTraceId={selectedTraceId}
            setSelectedTraceId={setSelectedTraceId}
            spans={spans}
            selectedSpan={selectedSpan as VisualizerSpanLite | null}
            setSelectedSpan={
              setSelectedSpan as (span: VisualizerSpanLite | null) => void
            }
            logs={logs}
            logsLoading={logsLoading}
            loading={loading}
            error={error}
            spansById={new Map(spans.map(s => [s.span_id, s]))}
          />
        ) : (
          <TacticGraphVisualization
            tacticGraph={tacticGraph}
            tacticGraphLoading={tacticGraphLoading}
            tacticGraphError={tacticGraphError}
            selectedTacticNode={selectedTacticNode}
            setSelectedTacticNode={setSelectedTacticNode}
            selectedTacticEdge={selectedTacticEdge}
            setSelectedTacticEdge={setSelectedTacticEdge}
          />
        )}
      </div>
    </Modal>
  );
};

// Traces Visualization Component
const TracesVisualization = ({
  traceIds,
  selectedTraceId,
  setSelectedTraceId,
  spans,
  enhancedSpans,
  selectedSpan,
  setSelectedSpan,
  logs,
  logsLoading,
  collapsedNodes,
  maxDepth,
  maxPossibleDepth,
  loading,
  error,
  successPathNodes,
  spansById,
  onToggleCollapse,
  onDepthChange,
}: {
  traceIds: string[];
  selectedTraceId: string;
  setSelectedTraceId: (id: string) => void;
  spans: VisualizerSpanLite[];
  enhancedSpans: EnhancedSpan[];
  selectedSpan: EnhancedSpan | null;
  setSelectedSpan: (span: EnhancedSpan | null) => void;
  logs: Record<string, unknown> | null;
  logsLoading: boolean;
  collapsedNodes: Set<string>;
  maxDepth: number | null;
  maxPossibleDepth: number;
  loading: boolean;
  error: string | null;
  successPathNodes: Set<string>;
  spansById: Map<string, EnhancedSpan>;
  onToggleCollapse: (spanId: string) => void;
  onDepthChange: (depth: number | null) => void;
}) => {
  return (
    <>
      <div className='flex-1 flex flex-col gap-3 min-w-0'>
        {/* Control Panel */}
        <div className='flex items-center gap-4 flex-wrap bg-elevation-surface-raised p-4 rounded-lg border border-elevation-surface-overlay'>
          {/* Trace Selection */}
          <div className='flex items-center gap-3 flex-1 min-w-[320px]'>
            {traceIds.length > 1 ? (
              <>
                <div className='text-sm text-text font-semibold'>Trace</div>
                <select
                  className='flex-1 h-9 rounded border border-elevation-surface-overlay bg-elevation-surface-sunken text-text px-2'
                  value={selectedTraceId}
                  onChange={e => setSelectedTraceId(e.target.value)}
                  disabled={!traceIds.length}
                >
                  {!traceIds.length ? (
                    <option value=''>(no traces)</option>
                  ) : null}
                  {traceIds.map(t => (
                    <option key={t} value={t}>
                      {t}
                    </option>
                  ))}
                </select>
              </>
            ) : traceIds.length === 1 ? (
              <div className='text-sm text-text'>
                <span className='font-semibold'>Trace:</span>{' '}
                <span className='font-mono text-text-disabled'>
                  {traceIds[0]}
                </span>
              </div>
            ) : (
              <div className='text-sm text-text-disabled'>No traces.</div>
            )}
          </div>

          {/* Depth Control */}
          {spans.length > 0 && (
            <div className='flex items-center gap-3'>
              <div className='text-sm text-text font-semibold'>Max Depth</div>
              <div className='flex gap-2'>
                {[1, 2, 3, 4, 5].map(depth => (
                  <button
                    key={depth}
                    onClick={() => onDepthChange(depth)}
                    disabled={depth > maxPossibleDepth}
                    className={`px-3 py-1.5 text-sm rounded border transition-colors ${
                      maxDepth === depth
                        ? 'bg-primary-default text-white border-primary-default'
                        : 'bg-elevation-surface-sunken text-text border-elevation-surface-overlay hover:bg-elevation-surface-overlay'
                    } ${depth > maxPossibleDepth ? 'opacity-40 cursor-not-allowed' : ''}`}
                  >
                    {depth}
                  </button>
                ))}
                <button
                  onClick={() => onDepthChange(null)}
                  className={`px-3 py-1.5 text-sm rounded border transition-colors ${
                    maxDepth === null
                      ? 'bg-primary-default text-white border-primary-default'
                      : 'bg-elevation-surface-sunken text-text border-elevation-surface-overlay hover:bg-elevation-surface-overlay'
                  }`}
                >
                  All
                </button>
              </div>
            </div>
          )}

          {/* Status indicators */}
          <div className='flex items-center gap-3'>
            {loading ? (
              <div className='text-sm text-text-disabled'>Loading…</div>
            ) : null}
            {error ? (
              <div className='text-sm text-text-danger'>{error}</div>
            ) : null}
            {enhancedSpans.length > 0 && (
              <div className='text-xs text-text-disabled'>
                {enhancedSpans.length} spans • {collapsedNodes.size} collapsed
              </div>
            )}
          </div>
        </div>

        <div className='flex-1 min-h-0'>
          <SpanGraphView
            spans={enhancedSpans}
            selectedSpanId={selectedSpan?.span_id}
            onSelectSpanId={spanId =>
              setSelectedSpan(spansById.get(spanId) ?? null)
            }
            successPathNodes={successPathNodes}
            collapsedNodes={collapsedNodes}
            onToggleCollapse={onToggleCollapse}
          />
        </div>
      </div>

      {/* Right panel - Span details and logs */}
      <div className='w-[480px] shrink-0 overflow-auto rounded-lg border border-elevation-surface-overlay bg-elevation-surface-sunken'>
        <div className='p-4 space-y-4'>
          {/* Span details section */}
          <div>
            <div className='flex items-center justify-between gap-2 mb-3'>
              <div className='text-sm text-text font-semibold'>
                Span details
              </div>
              {selectedSpan ? (
                <div className='text-xs text-text-disabled'>
                  {selectedSpan.service_name} •{' '}
                  {selectedSpan.span_id.slice(0, 12)}…
                </div>
              ) : null}
            </div>

            {selectedSpan ? (
              <div className='space-y-3'>
                <div>
                  <div className='text-sm text-text font-semibold'>
                    {selectedSpan.name}
                  </div>
                  <div className='text-xs text-text-disabled'>
                    {selectedSpan.service_name}
                  </div>
                </div>

                <div>
                  <div className='text-xs text-text-disabled mb-1'>
                    Attributes
                  </div>
                  <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded p-3 max-h-48 overflow-auto'>
                    <pre className='text-xs text-text whitespace-pre-wrap'>
                      {JSON.stringify(selectedSpan.attributes ?? {}, null, 2)}
                    </pre>
                  </div>
                </div>
              </div>
            ) : (
              <div className='text-sm text-text-disabled'>
                Select a span node to see details and logs.
              </div>
            )}
          </div>

          {/* Logs section */}
          <div className='border-t border-elevation-surface-overlay pt-4'>
            <div className='text-sm text-text font-semibold mb-3'>Logs</div>

            {!selectedSpan ? (
              <div className='text-sm text-text-disabled'>—</div>
            ) : logsLoading ? (
              <div className='flex items-center gap-2 text-sm text-text-disabled'>
                <div className='animate-spin rounded-full h-4 w-4 border-b-2 border-primary-default'></div>
                Loading logs…
              </div>
            ) : logs ? (
              <LogsDisplay logs={logs} />
            ) : (
              <div className='text-sm text-text-disabled'>No logs.</div>
            )}
          </div>
        </div>
      </div>
    </>
  );
};

// Copy Button Component
const CopyButton = ({ text }: { text: string }) => {
  const [copied, setCopied] = useState(false);

  const handleCopy = async () => {
    try {
      await navigator.clipboard.writeText(text);
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
    } catch (err) {
      // Failed to copy to clipboard
      setCopied(false);
    }
  };

  return (
    <button
      onClick={handleCopy}
      className='px-2 py-1 text-xs rounded bg-elevation-surface-raised border border-elevation-surface-overlay hover:bg-elevation-surface-overlay transition-colors'
      title='Copy to clipboard'
    >
      {copied ? '✓ Copied' : 'Copy'}
    </button>
  );
};

// JSON Viewer Component with syntax highlighting
const JsonViewer = ({ data }: { data: unknown }) => {
  const jsonString = useMemo(() => JSON.stringify(data, null, 2), [data]);

  // Simple syntax highlighting using regex
  const highlighted = useMemo(() => {
    return jsonString
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(
        /"([^"]+)":/g,
        '<span style="color: var(--color-text-information, #3b82f6)">"$1"</span>:'
      )
      .replace(
        /: "([^"]*)"/g,
        ': <span style="color: var(--color-text-success, #10b981)">"$1"</span>'
      )
      .replace(
        /: (true|false)/g,
        ': <span style="color: var(--color-text-warning, #d97706)">$1</span>'
      )
      .replace(
        /: (null)/g,
        ': <span style="color: var(--color-text-disabled, #9ca3af)">$1</span>'
      )
      .replace(
        /: (-?\d+\.?\d*)/g,
        ': <span style="color: var(--color-text-information, #3b82f6)">$1</span>'
      );
  }, [jsonString]);

  return (
    <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded p-3 max-h-96 overflow-auto'>
      <pre
        className='text-xs font-mono text-text whitespace-pre-wrap'
        dangerouslySetInnerHTML={{ __html: highlighted }}
      />
    </div>
  );
};

// Helper to extract focused goals from information
const extractFocusedGoals = (
  information: Record<string, unknown>
): string[] | null => {
  try {
    const result = information?.result as Record<string, unknown> | undefined;
    const proofState = result?.proof_state as
      | Record<string, unknown>
      | undefined;
    const focusedGoals = proofState?.focused_goals as unknown;

    if (Array.isArray(focusedGoals)) {
      return focusedGoals.map(goal => String(goal));
    }
    return null;
  } catch {
    return null;
  }
};

// Information Viewer with tabs for Focused Goals and JSON
const InformationViewer = ({
  data,
  title = 'Information',
}: {
  data: Record<string, unknown>;
  title?: string;
}) => {
  const [activeTab, setActiveTab] = useState<'goals' | 'json'>('goals');
  const focusedGoals = useMemo(() => extractFocusedGoals(data), [data]);

  return (
    <div>
      <div className='flex items-center justify-between mb-2'>
        <div className='text-xs text-text-disabled'>{title}</div>
        <CopyButton text={JSON.stringify(data, null, 2)} />
      </div>

      {focusedGoals && focusedGoals.length > 0 ? (
        <>
          {/* Tabs */}
          <div className='flex gap-2 mb-2 border-b border-elevation-surface-overlay'>
            <button
              onClick={() => setActiveTab('goals')}
              className={`px-3 py-1.5 text-xs font-medium transition-colors ${
                activeTab === 'goals'
                  ? 'text-text-information border-b-2 border-text-information'
                  : 'text-text-disabled hover:text-text'
              }`}
            >
              Focused Goals
            </button>
            <button
              onClick={() => setActiveTab('json')}
              className={`px-3 py-1.5 text-xs font-medium transition-colors ${
                activeTab === 'json'
                  ? 'text-text-information border-b-2 border-text-information'
                  : 'text-text-disabled hover:text-text'
              }`}
            >
              JSON
            </button>
          </div>

          {/* Tab Content */}
          {activeTab === 'goals' ? (
            <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded p-3 max-h-96 overflow-auto space-y-3'>
              {focusedGoals.map((goal, idx) => (
                <div
                  key={idx}
                  className='border-l-2 border-text-information pl-3'
                >
                  <div className='text-xs text-text-disabled mb-1'>
                    Goal {idx + 1}
                  </div>
                  <pre className='text-xs font-mono text-text whitespace-pre-wrap'>
                    {goal}
                  </pre>
                </div>
              ))}
            </div>
          ) : (
            <JsonViewer data={data} />
          )}
        </>
      ) : (
        <JsonViewer data={data} />
      )}
    </div>
  );
};

// Flamegraph Visualization Component
const FlamegraphVisualization = ({
  traceIds,
  selectedTraceId,
  setSelectedTraceId,
  spans,
  selectedSpan,
  setSelectedSpan,
  logs,
  logsLoading,
  loading,
  error,
  spansById,
}: {
  traceIds: string[];
  selectedTraceId: string;
  setSelectedTraceId: (id: string) => void;
  spans: VisualizerSpanLite[];
  selectedSpan: VisualizerSpanLite | null;
  setSelectedSpan: (span: VisualizerSpanLite | null) => void;
  logs: Record<string, unknown> | null;
  logsLoading: boolean;
  loading: boolean;
  error: string | null;
  spansById: Map<string, VisualizerSpanLite>;
}) => {
  return (
    <>
      <div className='flex-1 flex flex-col gap-3 min-w-0'>
        {/* Control Panel */}
        <div className='flex items-center gap-4 flex-wrap bg-elevation-surface-raised p-4 rounded-lg border border-elevation-surface-overlay'>
          {/* Trace Selection */}
          <div className='flex items-center gap-3 flex-1 min-w-[320px]'>
            {traceIds.length > 1 ? (
              <>
                <div className='text-sm text-text font-semibold'>Trace</div>
                <select
                  className='flex-1 h-9 rounded border border-elevation-surface-overlay bg-elevation-surface-sunken text-text px-2'
                  value={selectedTraceId}
                  onChange={e => setSelectedTraceId(e.target.value)}
                  disabled={!traceIds.length}
                >
                  {!traceIds.length ? (
                    <option value=''>(no traces)</option>
                  ) : null}
                  {traceIds.map(t => (
                    <option key={t} value={t}>
                      {t}
                    </option>
                  ))}
                </select>
              </>
            ) : traceIds.length === 1 ? (
              <div className='text-sm text-text'>
                <span className='font-semibold'>Trace:</span>{' '}
                <span className='font-mono text-text-disabled'>
                  {traceIds[0]}
                </span>
              </div>
            ) : (
              <div className='text-sm text-text-disabled'>No traces.</div>
            )}
          </div>

          {/* Status indicators */}
          <div className='flex items-center gap-3'>
            {loading ? (
              <div className='text-sm text-text-disabled'>Loading…</div>
            ) : null}
            {error ? (
              <div className='text-sm text-text-danger'>{error}</div>
            ) : null}
            {spans.length > 0 && (
              <div className='text-xs text-text-disabled'>
                {spans.length} spans
              </div>
            )}
          </div>
        </div>

        <div className='flex-1 min-h-0'>
          <FlamegraphView
            spans={spans}
            selectedSpanId={selectedSpan?.span_id}
            onSelectSpanId={spanId =>
              setSelectedSpan(spansById.get(spanId) ?? null)
            }
          />
        </div>
      </div>

      {/* Right panel - Span details and logs */}
      <div className='w-[480px] shrink-0 overflow-auto rounded-lg border border-elevation-surface-overlay bg-elevation-surface-sunken'>
        <div className='p-4 space-y-4'>
          {/* Span details section */}
          <div>
            <div className='flex items-center justify-between gap-2 mb-3'>
              <div className='text-sm text-text font-semibold'>
                Span details
              </div>
              {selectedSpan ? (
                <div className='text-xs text-text-disabled'>
                  {selectedSpan.service_name} •{' '}
                  {selectedSpan.span_id.slice(0, 12)}…
                </div>
              ) : null}
            </div>

            {selectedSpan ? (
              <div className='space-y-3'>
                <div>
                  <div className='text-sm text-text font-semibold'>
                    {selectedSpan.name}
                  </div>
                  <div className='text-xs text-text-disabled'>
                    {selectedSpan.service_name}
                  </div>
                </div>

                <div>
                  <div className='text-xs text-text-disabled mb-1'>
                    Attributes
                  </div>
                  <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded p-3 max-h-48 overflow-auto'>
                    <pre className='text-xs text-text whitespace-pre-wrap'>
                      {JSON.stringify(selectedSpan.attributes ?? {}, null, 2)}
                    </pre>
                  </div>
                </div>
              </div>
            ) : (
              <div className='text-sm text-text-disabled'>
                Select a span node to see details and logs.
              </div>
            )}
          </div>

          {/* Logs section */}
          <div className='border-t border-elevation-surface-overlay pt-4'>
            <div className='text-sm text-text font-semibold mb-3'>Logs</div>

            {!selectedSpan ? (
              <div className='text-sm text-text-disabled'>—</div>
            ) : logsLoading ? (
              <div className='flex items-center gap-2 text-sm text-text-disabled'>
                <div className='animate-spin rounded-full h-4 w-4 border-b-2 border-primary-default'></div>
                Loading logs…
              </div>
            ) : logs ? (
              <LogsDisplay logs={logs} />
            ) : (
              <div className='text-sm text-text-disabled'>No logs.</div>
            )}
          </div>
        </div>
      </div>
    </>
  );
};

// Tactic Graph Visualization Component
const TacticGraphVisualization = ({
  tacticGraph,
  tacticGraphLoading,
  tacticGraphError,
  selectedTacticNode,
  setSelectedTacticNode,
  selectedTacticEdge,
  setSelectedTacticEdge,
}: {
  tacticGraph: TacticGraphResponse | null;
  tacticGraphLoading: boolean;
  tacticGraphError: string | null;
  selectedTacticNode: string | null;
  setSelectedTacticNode: (nodeId: string | null) => void;
  selectedTacticEdge: string | null;
  setSelectedTacticEdge: (edgeId: string | null) => void;
}) => {
  const selectedNode = tacticGraph?.graph.nodes.find(
    n => n.id === selectedTacticNode
  );
  const selectedNodeEdges = tacticGraph?.graph.edges.filter(
    e => e.source === selectedTacticNode || e.target === selectedTacticNode
  );

  // Extract graph information in a type-safe way
  const graphInfo = useMemo(() => {
    if (!tacticGraph?.graph.information) return null;
    const info = tacticGraph.graph.information;
    return {
      cpp_code: typeof info.cpp_code === 'string' ? info.cpp_code : undefined,
      cpp_spec: typeof info.cpp_spec === 'string' ? info.cpp_spec : undefined,
      proofScript:
        typeof info.proofScript === 'string' ? info.proofScript : undefined,
      task_status: info.task_status,
      taskStatus: info.taskStatus,
      raw: info,
    };
  }, [tacticGraph]);

  // Find selected edge by matching the edge ID
  // We need to reconstruct the edge index to match
  const selectedEdge = useMemo(() => {
    if (!selectedTacticEdge || !tacticGraph) return null;

    // Extract the edge index from the ID
    const match = selectedTacticEdge.match(/^edge-(\d+)$/);
    if (!match) return null;

    const edgeIdx = parseInt(match[1], 10);

    // Reconstruct the edge groups to find the right edge
    const edgeGroups = new Map<string, typeof tacticGraph.graph.edges>();
    for (const edge of tacticGraph.graph.edges) {
      const key = `${edge.source}→${edge.target}`;
      if (!edgeGroups.has(key)) {
        edgeGroups.set(key, []);
      }
      edgeGroups.get(key)!.push(edge);
    }

    let currentIdx = 0;
    for (const [, groupEdges] of edgeGroups) {
      for (const edge of groupEdges) {
        if (currentIdx === edgeIdx) {
          return { edge, edgeId: selectedTacticEdge };
        }
        currentIdx++;
      }
    }
    return null;
  }, [selectedTacticEdge, tacticGraph]);

  return (
    <>
      <div className='flex-1 flex flex-col gap-3 min-w-0'>
        {/* Control Panel */}
        <div className='flex items-center gap-4 flex-wrap bg-elevation-surface-raised p-4 rounded-lg border border-elevation-surface-overlay'>
          {tacticGraphLoading ? (
            <div className='text-sm text-text-disabled'>
              Loading tactic graph…
            </div>
          ) : tacticGraphError ? (
            <div className='text-sm text-text-danger'>{tacticGraphError}</div>
          ) : tacticGraph ? (
            <>
              <div className='text-sm text-text font-semibold'>
                Task: {tacticGraph.task_name}
              </div>
              <div className='text-xs text-text-disabled'>
                {tacticGraph.total_nodes} nodes • {tacticGraph.total_edges}{' '}
                edges
              </div>
            </>
          ) : null}
        </div>

        {/* Graph Visualization */}
        <div className='flex-1 min-h-0'>
          {tacticGraphLoading ? (
            <div className='flex items-center justify-center h-full bg-elevation-surface-sunken rounded-lg border border-elevation-surface-overlay'>
              <div className='text-center'>
                <div className='animate-spin rounded-full h-8 w-8 border-b-2 border-primary-default mx-auto mb-4'></div>
                <div className='text-sm text-text-disabled'>
                  Loading tactic graph…
                </div>
              </div>
            </div>
          ) : tacticGraphError ? (
            <div className='flex items-center justify-center h-full bg-elevation-surface-sunken rounded-lg border border-elevation-surface-overlay'>
              <div className='text-center'>
                <div className='text-sm text-text-danger mb-2'>
                  {tacticGraphError}
                </div>
              </div>
            </div>
          ) : tacticGraph ? (
            <TacticGraphView
              graph={tacticGraph}
              selectedNodeId={selectedTacticNode || undefined}
              onSelectNodeId={nodeId => {
                setSelectedTacticNode(nodeId);
                if (nodeId !== null) {
                  setSelectedTacticEdge(null); // Clear edge selection only when selecting a node
                }
              }}
              selectedEdgeId={selectedTacticEdge || undefined}
              onSelectEdgeId={edgeId => {
                setSelectedTacticEdge(edgeId);
                if (edgeId !== null) {
                  setSelectedTacticNode(null); // Clear node selection only when selecting an edge
                }
              }}
            />
          ) : (
            <div className='flex items-center justify-center h-full bg-elevation-surface-sunken rounded-lg border border-elevation-surface-overlay'>
              <div className='text-sm text-text-disabled'>
                No tactic graph data available
              </div>
            </div>
          )}
        </div>
      </div>

      {/* Right panel - Node or Edge details */}
      <div className='w-[480px] shrink-0 overflow-auto rounded-lg border border-elevation-surface-overlay bg-elevation-surface-sunken'>
        <div className='p-4 space-y-4'>
          <div className='text-sm text-text font-semibold mb-3'>
            {selectedEdge
              ? 'Edge Details'
              : selectedNode
                ? 'Node Details'
                : 'Graph Information'}
          </div>
          {selectedEdge ? (
            <div className='space-y-3'>
              <div>
                <div className='text-xs text-text-disabled mb-1'>Edge ID</div>
                <div className='text-sm font-mono text-text'>
                  {selectedEdge.edgeId}
                </div>
              </div>
              <div>
                <div className='text-xs text-text-disabled mb-1'>Label</div>
                <div className='text-sm text-text font-semibold wrap-break-word bg-elevation-surface-raised p-3 rounded border border-elevation-surface-overlay max-h-32 overflow-auto'>
                  {selectedEdge.edge.label}
                </div>
              </div>
              <div>
                <div className='text-xs text-text-disabled mb-1'>
                  Source Node
                </div>
                <div className='text-xs font-mono text-text break-all bg-elevation-surface-raised p-2 rounded border border-elevation-surface-overlay'>
                  {selectedEdge.edge.source}
                </div>
              </div>
              <div>
                <div className='text-xs text-text-disabled mb-1'>
                  Target Node
                </div>
                <div className='text-xs font-mono text-text break-all bg-elevation-surface-raised p-2 rounded border border-elevation-surface-overlay'>
                  {selectedEdge.edge.target}
                </div>
              </div>
              {selectedEdge.edge.source === selectedEdge.edge.target && (
                <div className='text-xs text-text-warning bg-background-warning border border-border-warning rounded p-2'>
                  ⟲ Self-loop edge
                </div>
              )}
              <div>
                <InformationViewer
                  data={
                    selectedEdge.edge.information as Record<string, unknown>
                  }
                  title='Edge Information'
                />
              </div>
            </div>
          ) : selectedNode ? (
            <div className='space-y-3'>
              <div>
                <div className='text-xs text-text-disabled mb-1'>Node ID</div>
                <div className='text-sm font-mono text-text break-all'>
                  {selectedNode.id}
                </div>
              </div>
              {selectedNodeEdges && selectedNodeEdges.length > 0 && (
                <div>
                  <div className='text-xs text-text-disabled mb-1'>
                    Connected Edges ({selectedNodeEdges.length})
                  </div>
                  <div className='space-y-2 max-h-64 overflow-auto'>
                    {selectedNodeEdges.map((edge, idx) => {
                      const hasError =
                        edge.information?.error === 'true' ||
                        edge.information?.error === true;
                      return (
                        <div
                          key={idx}
                          className={`p-2 rounded border ${
                            hasError
                              ? 'border-border-warning bg-background-warning'
                              : 'border-elevation-surface-overlay bg-elevation-surface-raised'
                          } text-xs`}
                        >
                          <div className='font-semibold text-text mb-1'>
                            {edge.label}
                          </div>
                          <div className='text-text-disabled font-mono'>
                            {edge.source === selectedNode.id ? '→' : '←'}{' '}
                            {edge.source === selectedNode.id
                              ? edge.target.slice(0, 16)
                              : edge.source.slice(0, 16)}
                            ...
                          </div>
                          {hasError && (
                            <div className='text-xs text-text-warning mt-1'>
                              Error
                            </div>
                          )}
                        </div>
                      );
                    })}
                  </div>
                </div>
              )}
              <div>
                <InformationViewer
                  data={selectedNode.information as Record<string, unknown>}
                  title='Information'
                />
              </div>
            </div>
          ) : graphInfo ? (
            <>
              <div className='space-y-3'>
                {/* Graph-level Information */}
                {graphInfo.cpp_code && (
                  <div>
                    <div className='flex items-center justify-between mb-2'>
                      <div className='text-xs text-text-disabled'>C++ Code</div>
                      <CopyButton text={graphInfo.cpp_code} />
                    </div>
                    <CodeViewer code={graphInfo.cpp_code} language='cpp' />
                  </div>
                )}
                {graphInfo.cpp_spec && (
                  <div>
                    <div className='flex items-center justify-between mb-2'>
                      <div className='text-xs text-text-disabled'>
                        C++ Specification
                      </div>
                      <CopyButton text={graphInfo.cpp_spec} />
                    </div>
                    <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded p-3 max-h-64 overflow-auto'>
                      <pre className='text-xs font-mono text-text whitespace-pre-wrap'>
                        {graphInfo.cpp_spec}
                      </pre>
                    </div>
                  </div>
                )}
                {graphInfo.proofScript && (
                  <div>
                    <div className='flex items-center justify-between mb-2'>
                      <div className='text-xs text-text-disabled'>
                        Proof Script
                      </div>
                      <CopyButton text={graphInfo.proofScript} />
                    </div>
                    <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded p-3 max-h-64 overflow-auto'>
                      <pre className='text-xs font-mono text-text whitespace-pre-wrap'>
                        {graphInfo.proofScript}
                      </pre>
                    </div>
                  </div>
                )}
                {(graphInfo.task_status !== undefined ||
                  graphInfo.taskStatus !== undefined) && (
                  <div>
                    <div className='text-xs text-text-disabled mb-2'>
                      Task Status
                    </div>
                    <StatusBadge
                      status={
                        String(
                          graphInfo.taskStatus ?? graphInfo.task_status
                        ) === 'true'
                          ? 'Success'
                          : 'Failure'
                      }
                    />
                  </div>
                )}
                {/* Show all other fields as JSON */}
                <div>
                  <div className='flex items-center justify-between mb-2'>
                    <div className='text-xs text-text-disabled'>
                      Additional Information
                    </div>
                    <CopyButton text={JSON.stringify(graphInfo.raw, null, 2)} />
                  </div>
                  <JsonViewer data={graphInfo.raw} />
                </div>
              </div>
            </>
          ) : (
            <div className='text-sm text-text-disabled'>
              Select a node or edge to see details
            </div>
          )}
        </div>
      </div>
    </>
  );
};

// Component for better log display
const LogsDisplay = ({ logs }: { logs: Record<string, unknown> }) => {
  const [viewMode, setViewMode] = useState<'formatted' | 'raw'>('formatted');

  // Try to extract structured log data
  const logEntries = useMemo(() => {
    // Check if logs has a common structure
    if (Array.isArray(logs)) {
      return logs;
    }
    if (logs.data && Array.isArray(logs.data)) {
      return logs.data;
    }
    if (logs.logs && Array.isArray(logs.logs)) {
      return logs.logs;
    }
    if (logs.result && Array.isArray(logs.result)) {
      return logs.result;
    }
    return null;
  }, [logs]);

  if (viewMode === 'raw' || !logEntries) {
    return (
      <div>
        <div className='flex justify-end mb-2'>
          <button
            onClick={() =>
              setViewMode(viewMode === 'raw' ? 'formatted' : 'raw')
            }
            className='text-xs text-primary-default hover:text-primary-hovered'
          >
            {viewMode === 'raw' ? 'Try Formatted View' : 'Show Raw JSON'}
          </button>
        </div>
        <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded p-3 max-h-[400px] overflow-auto'>
          <pre className='text-xs text-text whitespace-pre-wrap'>
            {JSON.stringify(logs, null, 2)}
          </pre>
        </div>
      </div>
    );
  }

  return (
    <div>
      <div className='flex justify-between items-center mb-2'>
        <div className='text-xs text-text-disabled'>
          {logEntries.length} {logEntries.length === 1 ? 'entry' : 'entries'}
        </div>
        <button
          onClick={() => setViewMode('raw')}
          className='text-xs text-primary-default hover:text-primary-hovered'
        >
          Show Raw JSON
        </button>
      </div>
      <div className='space-y-2 max-h-[400px] overflow-auto'>
        {logEntries.map((entry, idx) => {
          const entryAny = entry as Record<string, unknown>;
          const timestamp =
            entryAny?.timestamp ||
            entryAny?.time ||
            (entryAny?.ts as ReactNode);
          const message = entryAny?.message || entryAny?.msg || entryAny?.body;
          const level = entryAny?.level || (entryAny?.severity as ReactNode);

          return (
            <div
              key={idx}
              className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded p-2.5 text-xs'
            >
              {timestamp && (
                <div className='text-text-disabled mb-1'>
                  {new Date(String(timestamp)).toLocaleString()}
                </div>
              )}
              {level && (
                <span
                  className={`inline-block px-2 py-0.5 rounded text-[10px] font-semibold mr-2 ${
                    level === 'error' || level === 'ERROR'
                      ? 'bg-background-danger text-text-danger'
                      : level === 'warn' || level === 'WARNING'
                        ? 'bg-background-warning text-text-warning'
                        : level === 'info' || level === 'INFO'
                          ? 'bg-background-information text-text-information'
                          : 'bg-elevation-surface-overlay text-text-disabled'
                  }`}
                >
                  {String(level)}
                </span>
              )}
              <div className='text-text whitespace-pre-wrap wrap-break-word'>
                {typeof message === 'string'
                  ? message
                  : JSON.stringify(entry, null, 2)}
              </div>
            </div>
          );
        })}
      </div>
    </div>
  );
};

function parsePath(v: unknown): string[] | null {
  if (!v) return null;
  if (Array.isArray(v)) {
    const out = v.filter(
      (x): x is string => typeof x === 'string' && x.length > 0
    );
    return out.length ? out : null;
  }
  if (typeof v === 'string') {
    try {
      const parsed = JSON.parse(v);
      if (Array.isArray(parsed)) {
        const out = parsed.filter(
          (x): x is string => typeof x === 'string' && x.length > 0
        );
        return out.length ? out : null;
      }
      return null;
    } catch {
      return null;
    }
  }
  return null;
}

function normalizeRunTimestampMs(v: string): number | undefined {
  const hasTz = /([zZ]|[+-]\\d{2}:\\d{2})$/.test(v);
  const s = hasTz ? v : `${v}Z`;
  const n = Date.parse(s);
  return Number.isFinite(n) ? n : undefined;
}

export default VisualizerModal;
