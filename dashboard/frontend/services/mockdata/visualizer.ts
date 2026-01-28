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
    // Level 1 - run_task
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
    // Level 2 - strategy_agent
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
    // Level 3 - verify_spec (Branch 1)
    {
      trace_id: traceId,
      span_id: '915d637a90cdaf4b',
      parent_span_id: '3ee71f77f450cfe2',
      name: 'verify_spec',
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
    // Level 4 - analyze_goal (under verify_spec)
    {
      trace_id: traceId,
      span_id: 'a1b2c3d4e5f6a7b8',
      parent_span_id: '915d637a90cdaf4b',
      name: 'analyze_goal',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586044785600000',
      end_time_unix_nano: '1767586044850000000',
      attributes: {
        'operation.type': 'manual',
        action: 'analyzing goal structure',
      },
    },
    // Level 5 - parse_hypothesis (under analyze_goal)
    {
      trace_id: traceId,
      span_id: 'b2c3d4e5f6a7b8c9',
      parent_span_id: 'a1b2c3d4e5f6a7b8',
      name: 'parse_hypothesis',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586044790000000',
      end_time_unix_nano: '1767586044820000000',
      attributes: {
        'operation.type': 'manual',
        action: 'parsing hypothesis',
      },
    },
    // Level 6 - type_check (under parse_hypothesis)
    {
      trace_id: traceId,
      span_id: 'c3d4e5f6a7b8c9d0',
      parent_span_id: 'b2c3d4e5f6a7b8c9',
      name: 'type_check',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586044795000000',
      end_time_unix_nano: '1767586044810000000',
      attributes: {
        'operation.type': 'manual',
        action: 'type checking',
      },
    },
    // Level 7 - unify_types (under type_check)
    {
      trace_id: traceId,
      span_id: 'd4e5f6a7b8c9d0e1',
      parent_span_id: 'c3d4e5f6a7b8c9d0',
      name: 'unify_types',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586044800000000',
      end_time_unix_nano: '1767586044805000000',
      attributes: {
        'operation.type': 'manual',
        action: 'unifying types',
      },
    },
    // Level 4 - generate_strategy (under verify_spec)
    {
      trace_id: traceId,
      span_id: 'e5f6a7b8c9d0e1f2',
      parent_span_id: '915d637a90cdaf4b',
      name: 'generate_strategy',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586044860000000',
      end_time_unix_nano: '1767586045000000000',
      attributes: {
        'operation.type': 'manual',
        action: 'generating proof strategy',
      },
    },
    // Level 3 - apply_tactics (Branch 2)
    {
      trace_id: traceId,
      span_id: '05d0be94fecd70a9',
      parent_span_id: '3ee71f77f450cfe2',
      name: 'apply_tactics',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045050240000',
      end_time_unix_nano: '1767586045112185900',
      attributes: {
        'operation.type': 'manual',
        'operation.name': 'strategy_agent/process',
        parent: '1',
        action: 'progress apply_tactics',
      },
    },
    // Level 4 - intro_pattern (under apply_tactics)
    {
      trace_id: traceId,
      span_id: 'f6a7b8c9d0e1f2a3',
      parent_span_id: '05d0be94fecd70a9',
      name: 'intro_pattern',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045055000000',
      end_time_unix_nano: '1767586045070000000',
      attributes: {
        'operation.type': 'manual',
        action: 'applying intro pattern',
      },
    },
    // Level 4 - destruct_cases (under apply_tactics)
    {
      trace_id: traceId,
      span_id: 'a7b8c9d0e1f2a3b4',
      parent_span_id: '05d0be94fecd70a9',
      name: 'destruct_cases',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045075000000',
      end_time_unix_nano: '1767586045110000000',
      attributes: {
        'operation.type': 'manual',
        action: 'destructing cases',
      },
    },
    // Level 5 - case_analysis (under destruct_cases)
    {
      trace_id: traceId,
      span_id: 'b8c9d0e1f2a3b4c5',
      parent_span_id: 'a7b8c9d0e1f2a3b4',
      name: 'case_analysis',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045080000000',
      end_time_unix_nano: '1767586045095000000',
      attributes: {
        'operation.type': 'manual',
        action: 'analyzing cases',
      },
    },
    // Level 3 - delayed_case (Branch 3)
    {
      trace_id: traceId,
      span_id: '4b93368f5e990355',
      parent_span_id: '3ee71f77f450cfe2',
      name: 'delayed_case',
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
    // Level 4 - smash_context (under delayed_case)
    {
      trace_id: traceId,
      span_id: 'c9d0e1f2a3b4c5d6',
      parent_span_id: '4b93368f5e990355',
      name: 'smash_context',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045120000000',
      end_time_unix_nano: '1767586045250000000',
      attributes: {
        'operation.type': 'manual',
        action: 'smashing context',
      },
    },
    // Level 5 - simplify_hypothesis (under smash_context)
    {
      trace_id: traceId,
      span_id: 'd0e1f2a3b4c5d6e7',
      parent_span_id: 'c9d0e1f2a3b4c5d6',
      name: 'simplify_hypothesis',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045130000000',
      end_time_unix_nano: '1767586045200000000',
      attributes: {
        'operation.type': 'manual',
        action: 'simplifying hypothesis',
      },
    },
    // Level 6 - rewrite_rules (under simplify_hypothesis)
    {
      trace_id: traceId,
      span_id: 'e1f2a3b4c5d6e7f8',
      parent_span_id: 'd0e1f2a3b4c5d6e7',
      name: 'rewrite_rules',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045140000000',
      end_time_unix_nano: '1767586045180000000',
      attributes: {
        'operation.type': 'manual',
        action: 'applying rewrite rules',
      },
    },
    // Level 7 - match_pattern (under rewrite_rules)
    {
      trace_id: traceId,
      span_id: 'f2a3b4c5d6e7f8a9',
      parent_span_id: 'e1f2a3b4c5d6e7f8',
      name: 'match_pattern',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045150000000',
      end_time_unix_nano: '1767586045170000000',
      attributes: {
        'operation.type': 'manual',
        action: 'pattern matching',
      },
    },
    // Level 8 - substitute (under match_pattern)
    {
      trace_id: traceId,
      span_id: 'a3b4c5d6e7f8a9b0',
      parent_span_id: 'f2a3b4c5d6e7f8a9',
      name: 'substitute',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045155000000',
      end_time_unix_nano: '1767586045165000000',
      attributes: {
        'operation.type': 'manual',
        action: 'substituting terms',
      },
    },
    // Level 4 - apply_lemma (under delayed_case)
    {
      trace_id: traceId,
      span_id: '7c8d9e0f1a2b3c4d',
      parent_span_id: '4b93368f5e990355',
      name: 'apply_lemma',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045260000000',
      end_time_unix_nano: '1767586045534000000',
      attributes: {
        'operation.type': 'manual',
        'operation.name': 'strategy_agent/process',
        parent: '2',
        action: 'progress (go using {2}apply_lemma.apply_lemma_A)',
        id: '3',
      },
    },
    // Level 5 - lookup_lemma (under apply_lemma)
    {
      trace_id: traceId,
      span_id: 'b4c5d6e7f8a9b0c1',
      parent_span_id: '7c8d9e0f1a2b3c4d',
      name: 'lookup_lemma',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045270000000',
      end_time_unix_nano: '1767586045350000000',
      attributes: {
        'operation.type': 'manual',
        action: 'looking up lemma',
      },
    },
    // Level 5 - instantiate_lemma (under apply_lemma)
    {
      trace_id: traceId,
      span_id: 'c5d6e7f8a9b0c1d2',
      parent_span_id: '7c8d9e0f1a2b3c4d',
      name: 'instantiate_lemma',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045360000000',
      end_time_unix_nano: '1767586045480000000',
      attributes: {
        'operation.type': 'manual',
        action: 'instantiating lemma',
      },
    },
    // Level 6 - unify_goals (under instantiate_lemma)
    {
      trace_id: traceId,
      span_id: 'd6e7f8a9b0c1d2e3',
      parent_span_id: 'c5d6e7f8a9b0c1d2',
      name: 'unify_goals',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045370000000',
      end_time_unix_nano: '1767586045450000000',
      attributes: {
        'operation.type': 'manual',
        action: 'unifying goals',
      },
    },
    // Level 5 - verify_preconditions (under apply_lemma)
    {
      trace_id: traceId,
      span_id: 'e7f8a9b0c1d2e3f4',
      parent_span_id: '7c8d9e0f1a2b3c4d',
      name: 'verify_preconditions',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045490000000',
      end_time_unix_nano: '1767586045530000000',
      attributes: {
        'operation.type': 'manual',
        action: 'verifying preconditions',
      },
    },
    // Level 3 - finalize_proof (Branch 4)
    {
      trace_id: traceId,
      span_id: '8d9e0f1a2b3c4d5e',
      parent_span_id: '3ee71f77f450cfe2',
      name: 'finalize_proof',
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
    // Level 4 - qed_check (under finalize_proof)
    {
      trace_id: traceId,
      span_id: 'f8a9b0c1d2e3f4a5',
      parent_span_id: '8d9e0f1a2b3c4d5e',
      name: 'qed_check',
      service_name: 'rocq_agent',
      start_time_unix_nano: '1767586045546000000',
      end_time_unix_nano: '1767586045549000000',
      attributes: {
        'operation.type': 'manual',
        action: 'checking qed',
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
