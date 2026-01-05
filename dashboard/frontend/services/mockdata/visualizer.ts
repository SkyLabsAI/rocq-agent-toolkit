import type {
  VisualizerSpanLite,
  VisualizerSpansResponse,
  VisualizerTraceIdsResponse,
} from '@/services/dataservice';

import { simulateDelay } from './generators';

/**
 * Mock trace IDs for a specific run
 * Returns the trace ID from the real Tempo data
 */
export const getTraceIdsForRunMock = async (
  runId: string,
  _opts?: {
    startMs?: number;
    endMs?: number;
    lookbackMinutes?: number;
    limit?: number;
  }
): Promise<VisualizerTraceIdsResponse> => {
  await simulateDelay(300, 700);

  // Use the actual trace ID from the Tempo data
  const traceIds = ['31c499406fe4d752fd14800a6f3d368a'];

  const response: VisualizerTraceIdsResponse = {
    run_id: runId,
    trace_ids: traceIds,
    total: traceIds.length,
  };

  return response;
};

/**
 * Mock spans for a specific trace
 * Generates spans based on real Tempo trace structure
 */
export const getParsedSpansForTraceMock = async (
  traceId: string
): Promise<VisualizerSpansResponse> => {
  await simulateDelay(400, 800);

  const spans: VisualizerSpanLite[] = [
    // Root span - Running pipeline
    {
      trace_id: traceId,
      span_id: '187328b9dca87028',
      parent_span_id: null,
      name: 'Running pipeline',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586003009012700',
      end_time_unix_nano: '1767586045667664100',
      attributes: {
        'function.name': 'run_config',
        'function.module': 'rocq_pipeline.task_runner',
        'run.id': 'f26c4a8c-3504-4148-bfad-d05dc82fea5e',
      },
    },
    // Child span - run_task
    {
      trace_id: traceId,
      span_id: '7babccb3646c374c',
      parent_span_id: '187328b9dca87028',
      name: 'run_task',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586003179055400',
      end_time_unix_nano: '1767586045564442400',
      attributes: {
        'function.name': 'run_task',
        'function.module': 'rocq_pipeline.task_runner',
        'task.id':
          'bhv/apps/vswitch/lib/port/proof/port/proof.v#lemma:get_notify_spec_ok',
      },
    },
    // Child span - strategy_agent
    {
      trace_id: traceId,
      span_id: '3ee71f77f450cfe2',
      parent_span_id: '7babccb3646c374c',
      name: 'strategy_agent',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586044736973600',
      end_time_unix_nano: '1767586045560535600',
      attributes: {
        'operation.type': 'manual',
        'operation.name': 'strategy_agent',
        root_id: '0',
      },
    },
    // Child span - strategy_agent/process (verify_spec with id 1)
    {
      trace_id: traceId,
      span_id: '915d637a90cdaf4b',
      parent_span_id: '3ee71f77f450cfe2',
      name: 'strategy_agent/process',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586044785502200',
      end_time_unix_nano: '1767586045004338400',
      attributes: {
        'operation.type': 'manual',
        'operation.name': 'strategy_agent/process',
        parent: '0',
        action: 'progress verify_spec',
        id: '1',
      },
    },
    // Child span - strategy_agent/process (verify_spec continuation)
    {
      trace_id: traceId,
      span_id: '05d0be94fecd70a9',
      parent_span_id: '3ee71f77f450cfe2',
      name: 'strategy_agent/process',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045050240000',
      end_time_unix_nano: '1767586045112185900',
      attributes: {
        'operation.type': 'manual',
        'operation.name': 'strategy_agent/process',
        parent: '1',
        action: 'progress verify_spec',
      },
    },
    // Child span - strategy_agent/process (go with id 2)
    {
      trace_id: traceId,
      span_id: '4b93368f5e990355',
      parent_span_id: '3ee71f77f450cfe2',
      name: 'strategy_agent/process',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045112291300',
      end_time_unix_nano: '1767586045534584000',
      attributes: {
        'operation.type': 'manual',
        'operation.name': 'strategy_agent/process',
        parent: '1',
        action: 'progress go',
        id: '2',
      },
    },
  ];

  return { spans };
};

/**
 * Mock logs for a specific span
 * Generates realistic log entries with proper structure
 */
export const getLogsBySpanMock = async (args: {
  service: string;
  traceId: string;
  spanId: string;
  startMs: number;
  endMs: number;
  limit?: number;
  direction?: 'backward' | 'forward';
}): Promise<Record<string, unknown>> => {
  await simulateDelay(200, 500);

  const numLogs = Math.min(
    Math.floor(Math.random() * 20) + 5,
    args.limit ?? 200
  );
  const logs = [];

  for (let i = 0; i < numLogs; i++) {
    const timestamp =
      args.startMs + ((args.endMs - args.startMs) / numLogs) * i;
    const logLevel = ['DEBUG', 'INFO', 'WARN', 'ERROR'][
      Math.floor(Math.random() * 4)
    ];

    logs.push({
      timestamp: new Date(timestamp).toISOString(),
      level: logLevel,
      message: `Log message ${i + 1} for span ${args.spanId.substring(0, 8)}`,
      service: args.service,
      trace_id: args.traceId,
      span_id: args.spanId,
      attributes: {
        'log.index': i,
        'log.total': numLogs,
      },
    });
  }

  const response = {
    logs,
    total: logs.length,
    service: args.service,
    trace_id: args.traceId,
    span_id: args.spanId,
  };

  return response;
};
