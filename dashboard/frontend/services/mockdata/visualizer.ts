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
        action: 'progress (go using {1}delayed_case.smash_delayed_case_B)',
        id: '2',
      },
    },
    // Child span - strategy_agent/process (go continuation with id 3)
    {
      trace_id: traceId,
      span_id: '7c8d9e0f1a2b3c4d',
      parent_span_id: '3ee71f77f450cfe2',
      name: 'strategy_agent/process',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045534685000',
      end_time_unix_nano: '1767586045545000000',
      attributes: {
        'operation.type': 'manual',
        'operation.name': 'strategy_agent/process',
        parent: '2',
        action: 'progress (go using {2}apply_lemma.apply_lemma_A)',
        id: '3',
      },
    },
    // Child span - strategy_agent/process (success node with id 4)
    {
      trace_id: traceId,
      span_id: '8d9e0f1a2b3c4d5e',
      parent_span_id: '3ee71f77f450cfe2',
      name: 'strategy_agent/process',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045545100000',
      end_time_unix_nano: '1767586045550000000',
      attributes: {
        'operation.type': 'manual',
        'operation.name': 'strategy_agent/process',
        parent: '3',
        action: 'progress (go using {3}simplify.simplify_B)',
        id: '4',
      },
    },
    // Child span - strategy_agent/process (error node - no id)
    {
      trace_id: traceId,
      span_id: '9e0f1a2b3c4d5e6f',
      parent_span_id: '3ee71f77f450cfe2',
      name: 'strategy_agent/process',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045550100000',
      end_time_unix_nano: '1767586045555000000',
      attributes: {
        'operation.type': 'manual',
        'operation.name': 'strategy_agent/process',
        parent: '2',
        action: 'progress (go using {2}failed_tactic.failed_tactic_X)',
      },
    },
    // Child span - strategy_agent/process (another branch with id 5)
    {
      trace_id: traceId,
      span_id: '0f1a2b3c4d5e6f7a',
      parent_span_id: '3ee71f77f450cfe2',
      name: 'strategy_agent/process',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045555200000',
      end_time_unix_nano: '1767586045560000000',
      attributes: {
        'operation.type': 'manual',
        'operation.name': 'strategy_agent/process',
        parent: '1',
        action: 'progress (go using {1}alternative_path.alternative_C)',
        id: '5',
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
