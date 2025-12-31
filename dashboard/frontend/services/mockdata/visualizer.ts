import type {
  VisualizerSpanLite,
  VisualizerSpansResponse,
  VisualizerTraceIdsResponse,
} from '@/services/dataservice';

import { generateHexString, simulateDelay } from './generators';

/**
 * Mock trace IDs for a specific run
 * Generates realistic trace IDs with proper structure
 */
export const getTraceIdsForRunMock = async (
  runId: string,
  opts?: {
    startMs?: number;
    endMs?: number;
    lookbackMinutes?: number;
    limit?: number;
  }
): Promise<VisualizerTraceIdsResponse> => {
  await simulateDelay(300, 700);

  const limit = opts?.limit ?? 25;
  const numTraces = Math.min(Math.floor(Math.random() * 10) + 5, limit); // 5-15 traces, capped at limit

  const traceIds = Array.from({ length: numTraces }, (_, _i) => {
    // Generate realistic trace IDs (32 hex chars)
    return generateHexString(32);
  });

  const response: VisualizerTraceIdsResponse = {
    run_id: runId,
    trace_ids: traceIds,
    total: traceIds.length,
  };

  console.log(`Fetched ${traceIds.length} trace IDs for run ${runId} (MOCK)`);
  return response;
};

/**
 * Mock spans for a specific trace
 * Generates a hierarchical tree of spans with realistic timing
 */
export const getParsedSpansForTraceMock = async (
  traceId: string
): Promise<VisualizerSpansResponse> => {
  await simulateDelay(400, 800);

  const now = Date.now() * 1_000_000; // Convert to nanoseconds
  const spans: VisualizerSpanLite[] = [];

  // Root span - main agent execution
  const rootSpanId = generateHexString(16);
  const rootStartTime = now - 5_000_000_000; // 5 seconds ago
  const rootEndTime = now;

  spans.push({
    trace_id: traceId,
    span_id: rootSpanId,
    parent_span_id: null,
    name: 'agent.execute',
    service_name: 'rocq-agent',
    start_time_unix_nano: rootStartTime.toString(),
    end_time_unix_nano: rootEndTime.toString(),
    attributes: {
      'agent.name': 'ProofBot-v2.1',
      'agent.version': '2.1.0',
      'task.id': `task_${Math.floor(Math.random() * 100)}`,
      'task.type': 'FullProofTask',
    },
  });

  // Child spans - various operations
  const operations = [
    {
      name: 'llm.inference',
      service: 'llm-service',
      duration: 1_200_000_000,
      attributes: {
        'llm.model': 'gpt-4',
        'llm.input_tokens': 1250,
        'llm.output_tokens': 450,
        'llm.temperature': 0.7,
      },
    },
    {
      name: 'coq.compile',
      service: 'coq-service',
      duration: 800_000_000,
      attributes: {
        'coq.version': '8.17',
        'coq.file': 'theorem_001.v',
      },
    },
    {
      name: 'tactic.apply',
      service: 'rocq-agent',
      duration: 600_000_000,
      attributes: {
        'tactic.name': 'induction',
        'tactic.complexity': 7,
        'tactic.confidence': 0.89,
      },
    },
    {
      name: 'proof.validate',
      service: 'coq-service',
      duration: 450_000_000,
      attributes: {
        'proof.status': 'success',
        'proof.steps': 12,
      },
    },
    {
      name: 'cache.lookup',
      service: 'cache-service',
      duration: 50_000_000,
      attributes: {
        'cache.hit': true,
        'cache.key': 'proof_cache_001',
      },
    },
  ];

  let currentTime = rootStartTime + 100_000_000; // Start 100ms after root
  operations.forEach((op, _index) => {
    const spanId = generateHexString(16);
    const startTime = currentTime;
    const endTime = startTime + op.duration;

    spans.push({
      trace_id: traceId,
      span_id: spanId,
      parent_span_id: rootSpanId,
      name: op.name,
      service_name: op.service,
      start_time_unix_nano: startTime.toString(),
      end_time_unix_nano: endTime.toString(),
      attributes: op.attributes,
    });

    // Add nested spans for LLM inference
    if (op.name === 'llm.inference') {
      const nestedOps = [
        { name: 'llm.tokenize', duration: 100_000_000 },
        { name: 'llm.forward_pass', duration: 900_000_000 },
        { name: 'llm.decode', duration: 150_000_000 },
      ];

      let nestedTime = startTime + 10_000_000;
      nestedOps.forEach(nested => {
        const nestedSpanId = generateHexString(16);
        spans.push({
          trace_id: traceId,
          span_id: nestedSpanId,
          parent_span_id: spanId,
          name: nested.name,
          service_name: op.service,
          start_time_unix_nano: nestedTime.toString(),
          end_time_unix_nano: (nestedTime + nested.duration).toString(),
          attributes: {
            'operation.type': 'nested',
          },
        });
        nestedTime += nested.duration + 5_000_000; // Small gap between ops
      });
    }

    currentTime = endTime + 50_000_000; // 50ms gap between operations
  });

  console.log(`Fetched ${spans.length} spans for trace ${traceId} (MOCK)`);
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

  console.log(
    `Fetched ${logs.length} logs for span ${args.spanId.substring(0, 8)} (MOCK)`
  );
  return response;
};
