import axios from 'axios';

import { config } from '@/config/environment';
// Import mock data functions
import {
  getLogsBySpanMock,
  getParsedSpansForTraceMock,
  getTraceIdsForRunMock,
} from '@/services/mockdata';

const USE_MOCK_DATA = config.USE_MOCK_DATA || process.env.NODE_ENV === 'test';

export type VisualizerTraceIdsResponse = {
  run_id: string;
  trace_ids: string[];
  total: number;
};

export type VisualizerSpanLite = {
  trace_id: string;
  span_id: string;
  parent_span_id?: string | null;
  name: string;
  service_name: string;
  start_time_unix_nano?: string | null;
  end_time_unix_nano?: string | null;
  attributes?: Record<string, unknown>;
};

export type VisualizerSpansResponse = {
  spans: VisualizerSpanLite[];
};

// ========================================
// GET TRACE IDS FOR RUN
// ========================================

const getTraceIdsForRunReal = async (
  runId: string,
  opts?: {
    startMs?: number;
    endMs?: number;
    lookbackMinutes?: number;
    limit?: number;
  }
): Promise<VisualizerTraceIdsResponse> => {
  const lookbackMinutes = opts?.lookbackMinutes ?? 15;
  const limit = opts?.limit ?? 25;
  const url = new URL(
    `${config.DATA_API}/visualizer/data/runs/${encodeURIComponent(runId)}/trace-ids`
  );
  url.searchParams.set('limit', `${limit}`);
  if (opts?.startMs != null && opts?.endMs != null) {
    url.searchParams.set('start_ms', `${opts.startMs}`);
    url.searchParams.set('end_ms', `${opts.endMs}`);
  } else {
    url.searchParams.set('lookback_minutes', `${lookbackMinutes}`);
  }
  const resp = await axios.get(url.toString());
  return resp.data as VisualizerTraceIdsResponse;
};

export async function getTraceIdsForRun(
  runId: string,
  opts?: {
    startMs?: number;
    endMs?: number;
    lookbackMinutes?: number;
    limit?: number;
  }
): Promise<VisualizerTraceIdsResponse> {
  return USE_MOCK_DATA
    ? getTraceIdsForRunMock(runId, opts)
    : getTraceIdsForRunReal(runId, opts);
}

// ========================================
// GET PARSED SPANS FOR TRACE
// ========================================

const getParsedSpansForTraceReal = async (
  traceId: string
): Promise<VisualizerSpansResponse> => {
  const url = `${config.DATA_API}/visualizer/data/tempo/traces/${encodeURIComponent(
    traceId
  )}/spans`;
  const resp = await axios.get(url);
  return resp.data as VisualizerSpansResponse;
};

export async function getParsedSpansForTrace(
  traceId: string
): Promise<VisualizerSpansResponse> {
  return USE_MOCK_DATA
    ? getParsedSpansForTraceMock(traceId)
    : getParsedSpansForTraceReal(traceId);
}

// ========================================
// GET LOGS BY SPAN
// ========================================

const getLogsBySpanReal = async (args: {
  service: string;
  traceId: string;
  spanId: string;
  startMs: number;
  endMs: number;
  limit?: number;
  direction?: 'backward' | 'forward';
}): Promise<Record<string, unknown>> => {
  const url = new URL(`${config.DATA_API}/visualizer/data/logs/by-span`);
  url.searchParams.set('service', args.service);
  url.searchParams.set('trace_id', args.traceId);
  url.searchParams.set('span_id', args.spanId);
  url.searchParams.set('start_ms', `${args.startMs}`);
  url.searchParams.set('end_ms', `${args.endMs}`);
  url.searchParams.set('limit', `${args.limit ?? 200}`);
  url.searchParams.set('direction', args.direction ?? 'backward');
  const resp = await axios.get(url.toString());
  return resp.data as Record<string, unknown>;
};

export async function getLogsBySpan(args: {
  service: string;
  traceId: string;
  spanId: string;
  startMs: number;
  endMs: number;
  limit?: number;
  direction?: 'backward' | 'forward';
}): Promise<Record<string, unknown>> {
  return USE_MOCK_DATA ? getLogsBySpanMock(args) : getLogsBySpanReal(args);
}
