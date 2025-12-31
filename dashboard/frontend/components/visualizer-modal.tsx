'use client';

import { type ReactNode, useEffect, useMemo, useState } from 'react';

import Modal from '@/components/base/ui/modal';
import SpanGraphView from '@/components/visualizer/span-graph-view';
import {
  getLogsBySpan,
  getParsedSpansForTrace,
  getTraceIdsForRun,
  type VisualizerSpanLite,
} from '@/services/visualizer';

type Props = {
  isOpen: boolean;
  onClose: () => void;
  runId: string;
  runTimestampUtc: string;
};

const VisualizerModal = ({
  isOpen,
  onClose,
  runId,
  runTimestampUtc,
}: Props) => {
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const [traceIds, setTraceIds] = useState<string[]>([]);
  const [selectedTraceId, setSelectedTraceId] = useState<string>('');

  const [spans, setSpans] = useState<VisualizerSpanLite[]>([]);
  const [selectedSpan, setSelectedSpan] = useState<VisualizerSpanLite | null>(
    null
  );
  const [logs, setLogs] = useState<Record<string, unknown> | null>(null);
  const [logsLoading, setLogsLoading] = useState(false);

  // New states for collapsible nodes and depth control
  const [collapsedNodes, setCollapsedNodes] = useState<Set<string>>(new Set());
  const [maxDepth, setMaxDepth] = useState<number | null>(null);

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
  }, [isOpen, runId]);

  // Auto-load trace ids for this run.
  useEffect(() => {
    if (!isOpen) return;
    let cancelled = false;

    async function load() {
      setLoading(true);
      setError(null);
      try {
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
  }, [isOpen, runId, range.startMs, range.endMs]);

  // Fetch spans for selected trace id.
  useEffect(() => {
    if (!isOpen) return;
    if (!selectedTraceId) return;
    let cancelled = false;

    async function loadSpans() {
      setLoading(true);
      setError(null);
      setSpans([]);
      setSelectedSpan(null);
      setLogs(null);
      try {
        const res = await getParsedSpansForTrace(selectedTraceId);
        if (cancelled) return;
        setSpans(res.spans ?? []);
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
    () => new Map(spans.map(s => [s.span_id, s] as const)),
    [spans]
  );

  const successPathNodes = useMemo(() => {
    const out = new Set<string>();
    for (const s of spans) {
      const raw = s.attributes?.['search.path'];
      if (!raw) continue;
      const parsed = parsePath(raw);
      if (!parsed) continue;
      for (const n of parsed) out.add(n);
    }
    return out;
  }, [spans]);

  // Handler to toggle node collapse
  const toggleNodeCollapse = (spanId: string) => {
    setCollapsedNodes(prev => {
      const newSet = new Set(prev);
      const isCurrentlyCollapsed = newSet.has(spanId);

      if (isCurrentlyCollapsed) {
        // Expanding: remove from collapsed set
        newSet.delete(spanId);

        // Auto-collapse direct children (so they appear but are collapsed)
        const directChildren = spans
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
    const depths = calculateNodeDepths(spans);
    return depths.size > 0 ? Math.max(...Array.from(depths.values())) : 0;
  }, [spans]);

  return (
    <Modal
      isOpen={isOpen}
      onClose={onClose}
      title={`Visualizer - ${runId}`}
      size='full'
    >
      <div className='flex gap-4 h-[80vh]'>
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
                      onClick={() => handleDepthChange(depth)}
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
                    onClick={() => handleDepthChange(null)}
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
              {spans.length > 0 && (
                <div className='text-xs text-text-disabled'>
                  {spans.length} spans • {collapsedNodes.size} collapsed
                </div>
              )}
            </div>
          </div>

          <div className='flex-1 min-h-0'>
            <SpanGraphView
              spans={spans}
              selectedSpanId={selectedSpan?.span_id}
              onSelectSpanId={spanId =>
                setSelectedSpan(spansById.get(spanId) ?? null)
              }
              successPathNodes={successPathNodes}
              collapsedNodes={collapsedNodes}
              onToggleCollapse={toggleNodeCollapse}
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
      </div>
    </Modal>
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
