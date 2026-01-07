/** Per-task output format of the Rocq pipeline. */

/**
 * Kind of task.
 */
export type TaskKind =
  | {
      /** Fully proving a Rocq goal. */
      kind: 'FullProofTask';
    }
  | {
      /** User defined task kind. */
      kind: 'OtherTask';
      value: string;
    }
  | string;

/**
 * Task status upon completion.
 */
export type TaskStatus =
  | 'Success' /** Task completed successfully. */
  | 'Failure'; /** Task failed. */

/**
 * Kind of resource exhaustion.
 */
export type ResourceExhaustionKind =
  | {
      /** Exceeded timelimit in seconds. */
      kind: 'Timeout';
      value: number; // int
    }
  | {
      /** Exceeded LLM call limit. */
      kind: 'MaxLLMCalls';
      value: number; // int
    };

/**
 * Reason for task failure.
 */
export type FailureReason =
  | string[]
  | {
      /** Resource exhaustion. */
      kind: 'ResourceExhaustion';
      value: ResourceExhaustionKind;
    }
  | {
      /** Unrecoverable error. */
      kind: 'ExecutionError';
      value: string;
    }
  | {
      /** User defined failure reason. */
      kind: 'Other';
      value: string;
    };

/**
 * Aggregated LLM token metrics for task.
 */
export interface TokenCounts {
  /** Total LLM input tokens for task. */
  input_tokens: number; // int
  /** Total LLM output tokens for task. */
  output_tokens: number; // int
  /** Total LLM tokens for task. */
  total_tokens: number; // int
}

/**
 * Aggregated execution time metrics for task.
 */
export interface ResourceUsage {
  /** Total execution time for task. */
  execution_time_sec: number; // float
  /** Total CPU execution time for task. */
  cpu_time_sec: number; // float
  /** Total GPU execution time for task. */
  gpu_time_sec: number; // float
}

/**
 * Aggregated metrics for task.
 */
export interface Metrics {
  /** Total LLM calls for task. */
  llm_invocation_count: number; // int
  /** Aggregated LLM token metrics for task. */
  token_counts: TokenCounts;
  /** Aggregated execution time metrics for task. */
  resource_usage: ResourceUsage;
  /** Additional user defined metrics. (Mapped from 'abstract') */
  custom: Record<string, unknown> | null;
  /** Custom metrics for additional user-defined measurements */
  custom_metrics?: Record<string, unknown>;
  /** Timestamp when metrics were recorded */
  timestamp?: string;
}

export interface Details {
  cppCode: string;
  targetContent?: string;
  lemmaContent?: string;
  statesContent?: string;
}

/**
 * Side effects structure containing document interactions and other effects.
 */
export interface SideEffects {
  /** Document interaction results from the agent. */
  doc_interaction?: unknown;
  /** Additional side effects. */
  [key: string]: unknown;
}

/**
 * Task results structure containing side effects and other results.
 */
export interface TaskResults {
  /** Side effects produced during task execution. */
  side_effects?: SideEffects;
  /** Additional results. */
  [key: string]: unknown;
}

/**
 * Agent output for a single task.
 */
export interface TaskOutput {
  /** Unique identifier for the run (UUID). */
  run_id: string;
  /** Kind of task. */
  task_kind: TaskKind;
  /** Unique task identifier (file+task locator). */
  task_id: string;
  /** Unique trace identifier for corresponding opentelemetry output. */
  trace_id?: string;
  /** Timestamp when task began (ISO 8601). */
  timestamp_utc: string;
  /** Unique name of the agent that attempted the task. */
  agent_name: string;
  /** Task status upon completion. */
  status: TaskStatus;
  /** Reason for task failure. */
  failure_reason?: FailureReason;
  /** Agent results after task completion. (Mapped from 'abstract') */
  results: TaskResults | null;
  /** Aggregated metrics for task. */
  metrics: Metrics;

  details?: Details;

  metadata?: {
    tags: Record<string, string>;
    [key: string]: unknown;
  };
}

/**
 * Represents a batch of results from an agent or a run.
 */
export interface AgentResults {
  /** The name of the agent or batch run. */
  name: string;
  verified: boolean;
  organization: string;
  avgSuccessRate: number;
  tasksAttempted: number;
  avgExecutionTime: number;
  avgTokensUsed: number;
  avgLLMCalls: number;
  failures: FailureReason[];
  runs: AgentRun[];
}

export interface AgentRunOld {
  id: string;
  name: string;
  data: TaskOutput[];
}

export interface AgentSummary {
  cls_checksum: string;
  cls_name: string;
  cls_provenance: Record<string, unknown>;
  total_runs: number;
  best_run?: {
    run_id: string;
    agent_cls_checksum: string;
    agent_checksum: string;
    timestamp_utc: string;
    total_tasks: number;
    success_count: number;
    failure_count: number;
    success_rate: number;
    score: number;
    avg_total_tokens: number;
    avg_cpu_time_sec: number;
    avg_llm_invocation_count: number;
    metadata: {
      tags: Record<string, unknown>;
    };
  };
}

export interface AgentInstanceSummary {
  agent_checksum: string;
  cls_checksum: string;
  name: string;
  provenance: Record<string, unknown>;
  total_runs: number;
  best_run?: {
    run_id: string;
    agent_cls_checksum: string;
    agent_checksum: string;
    timestamp_utc: string;
    dataset_id?: string;
    total_tasks: number;
    success_count: number;
    failure_count: number;
    success_rate: number;
    score: number;
    avg_total_tokens: number;
    avg_cpu_time_sec: number;
    avg_llm_invocation_count: number;
    best_run: boolean;
    metadata: {
      tags: Record<string, unknown>;
    };
  };
}

export interface AgentRun {
  run_id: string;
  agent_name: string;
  timestamp_utc: string; // ISO 8601 date-time string
  total_tasks: number;
  success_count: number;
  failure_count: number;
  dataset_id: string;
  metadata: {
    tags?: Record<string, string>;
  };
}

export type Run = AgentRun;

export interface RunDetailsResponse {
  run_id: string;
  agent_name: string;
  total_tasks: number;
  tasks: TaskOutput[];
  metadata?: {
    tags: Record<string, string>;
    [key: string]: unknown;
  };
}

/**
 * The final structure: an array of AgentResults.
 */
export type AgentResultsArray = AgentResults[];

/**
 * Represents a benchmark or task set
 */
export interface Benchmark {
  dataset_id: string;
  description?: string;
  created_at: string;
}

/**
 * Represents a project that contains datasets
 */
export interface TaskSet {
  taskset_id: string;
  name: string;
  description?: string;
  created_at: string;
}

/**
 * Represents an agent instance in a taskset
 */
export interface TaskSetAgentInstance {
  agent_instance_id: string;
  agent_name: string;
  agent_checksum: string;
  run_id: string;
}

/**
 * Represents a task in a taskset
 */
export interface TaskSetTask {
  task_id: string;
  task_kind?: TaskKind;
  dataset_id?: string;
  tags?: Record<string, string>;
}

/**
 * Represents a task result for a specific agent instance
 */
export interface TaskSetTaskResult {
  task_id: string;
  agent_instance_id: string;
  success_count: number;
  total_count: number;
}

/**
 * Represents the results matrix for a taskset
 */
export interface TaskSetResults {
  taskset_id: string;
  tasks: TaskSetTask[];
  agent_instances: TaskSetAgentInstance[];
  results: TaskSetTaskResult[];
}
