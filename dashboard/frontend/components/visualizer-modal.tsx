'use client';

import React, { useEffect, useMemo, useState } from 'react';

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

export default function VisualizerModal({
  isOpen,
  onClose,
  runId,
  runTimestampUtc,
}: Props) {
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

  return (
    <Modal
      isOpen={isOpen}
      onClose={onClose}
      title={`Visualizer - ${runId}`}
      size='full'
    >
      <div className='flex gap-4 h-[80vh]'>
        <div className='flex-1 flex flex-col gap-3 min-w-0'>
          <div className='flex items-center gap-3 flex-wrap'>
            {traceIds.length > 1 ? (
              <>
                <div className='text-sm text-text font-semibold'>Trace</div>
                <select
                  className='h-9 rounded border border-elevation-surface-overlay bg-elevation-surface-raised text-text px-2 min-w-[420px]'
                  value={selectedTraceId}
                  onChange={e => setSelectedTraceId(e.target.value)}
                  disabled={!traceIds.length}
                >
                  {!traceIds.length ? <option value=''>(no traces)</option> : null}
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
                <span className='font-mono text-text-disabled'>{traceIds[0]}</span>
              </div>
            ) : (
              <div className='text-sm text-text-disabled'>No traces.</div>
            )}

            {loading ? <div className='text-sm text-text-disabled'>Loading…</div> : null}
            {error ? <div className='text-sm text-text-danger'>{error}</div> : null}
          </div>

          <div className='flex-1 min-h-0'>
            <SpanGraphView
              spans={spans}
              selectedSpanId={selectedSpan?.span_id}
              onSelectSpanId={spanId =>
                setSelectedSpan(spansById.get(spanId) ?? null)
              }
              successPathNodes={successPathNodes}
            />
          </div>
        </div>

        <div className='w-[420px] shrink-0 overflow-auto rounded-lg border border-elevation-surface-overlay bg-elevation-surface-sunken p-3'>
          <div className='flex items-center justify-between gap-2'>
            <div className='text-sm text-text font-semibold'>Span details</div>
            {selectedSpan ? (
              <div className='text-xs text-text-disabled'>
                {selectedSpan.service_name} • {selectedSpan.span_id.slice(0, 12)}…
              </div>
            ) : null}
          </div>

          {selectedSpan ? (
            <div className='mt-2'>
              <div className='text-sm text-text font-semibold'>
                {selectedSpan.name}
              </div>
              <div className='text-xs text-text-disabled'>
                {selectedSpan.service_name}
              </div>
              <div className='mt-2 text-xs text-text-disabled'>Attributes</div>
              <pre className='text-xs text-text whitespace-pre-wrap bg-elevation-surface-raised border border-elevation-surface-overlay rounded p-2 max-h-40 overflow-auto'>
                {JSON.stringify(selectedSpan.attributes ?? {}, null, 2)}
              </pre>
            </div>
          ) : (
            <div className='text-sm text-text-disabled mt-3'>
              Select a span node to see details and logs.
            </div>
          )}

          <div className='mt-4 border-t border-elevation-surface-overlay pt-3'>
            <div className='text-sm text-text font-semibold'>Logs</div>
          </div>

          {!selectedSpan ? (
            <div className='text-sm text-text-disabled mt-2'>—</div>
          ) : logsLoading ? (
            <div className='text-sm text-text-disabled mt-2'>Loading logs…</div>
          ) : logs ? (
            <pre className='text-xs text-text whitespace-pre-wrap mt-2'>
              {JSON.stringify(logs, null, 2)}
            </pre>
          ) : (
            <div className='text-sm text-text-disabled mt-2'>No logs.</div>
          )}
        </div>
      </div>
    </Modal>
  );
}

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


