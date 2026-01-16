import axios from 'axios';

import { config } from '@/config/environment';
import {
  bulkAddTagsMock,
  getAgentClassDataMock,
  getAgentInstancesMock,
  getAgentInstanceTaskRunsMock,
  getBenchmarkAgentsMock,
  getBenchmarksMock,
  getDatasetAgentInstancesMock,
  getDatasetInstanceRunsMock,
  getDetailsForDatasetMock,
  getDetailsMock,
  getObservabilityLogsMock,
  getProjectDatasetsMock,
  getProjectResultsMock,
  getProjectsMock,
  getRunDetailsMock,
  getRunsByInstanceMock,
  getTaskDetailsMock,
  refreshDataMock,
  uploadTasksYamlMock,
} from '@/services/mockdata';
import {
  type AgentInstanceSummary,
  type AgentRun,
  type AgentSummary,
  type Benchmark,
  type RunDetailsResponse,
  type TaskOutput,
  type TaskSet,
  type TaskSetResults,
} from '@/types/types';

// Check if we should use mock data
const USE_MOCK_DATA = config.USE_MOCK_DATA;

// ========================================
// AGENT CLASS API
// ========================================

const getAgentClassDataReal: () => Promise<AgentSummary[]> = async () => {
  const response = await axios.get(`${config.DATA_API}/agents/class`);
  return response.data as AgentSummary[];
};

export const getAgentClassData = USE_MOCK_DATA
  ? getAgentClassDataMock
  : getAgentClassDataReal;

// ========================================
// AGENT INSTANCES API
// ========================================

const getAgentInstancesReal = async (
  agentClsChecksum: string
): Promise<AgentInstanceSummary[]> => {
  const response = await axios.get(
    `${config.DATA_API}/agents/class/${agentClsChecksum}/instances`
  );
  return response.data as AgentInstanceSummary[];
};

export const getAgentInstances = USE_MOCK_DATA
  ? getAgentInstancesMock
  : getAgentInstancesReal;

// ========================================
// RUNS BY INSTANCE API
// ========================================

const getRunsByInstanceReal = async (
  agentChecksum: string
): Promise<AgentRun[]> => {
  const response = await axios.get(
    `${config.DATA_API}/agents/instance/${agentChecksum}/runs`
  );
  return response.data as AgentRun[];
};

export const getRunsByInstance = USE_MOCK_DATA
  ? getRunsByInstanceMock
  : getRunsByInstanceReal;

const getAgentInstanceTaskRunsReal = async (
  agentChecksum: string,
  taskId: number
): Promise<AgentRun[]> => {
  const response = await axios.get<{
    agent_checksum: string;
    task_id: number;
    task_name: string;
    run_ids: string[];
    total_runs: number;
  }>(
    `${config.DATA_API}/agents/instance/${agentChecksum}/tasks/${taskId}/runs`
  );

  if (response.data.run_ids.length === 0) {
    return [];
  }

  // Fetch full run details using batch endpoint
  const runIdsParam = response.data.run_ids.join(',');
  const detailsResponse = await axios.get<RunDetailsResponse[]>(
    `${config.DATA_API}/runs/details?run_ids=${runIdsParam}`
  );

  // Convert RunDetailsResponse to AgentRun format
  return detailsResponse.data.map(run => {
    const successCount = run.tasks.filter(t => t.status === 'Success').length;
    const failureCount = run.tasks.filter(t => t.status !== 'Success').length;
    // Get timestamp from first task if available
    const timestampUtc =
      run.tasks.length > 0
        ? run.tasks[0].timestamp_utc
        : new Date().toISOString();

    return {
      run_id: run.run_id,
      agent_name: run.agent_name,
      timestamp_utc: timestampUtc,
      total_tasks: run.tasks.length,
      success_count: successCount,
      failure_count: failureCount,
      dataset_id: '',
      metadata: {
        tags: run.metadata?.tags || {},
      },
    };
  });
};

export const getAgentInstanceTaskRuns = USE_MOCK_DATA
  ? getAgentInstanceTaskRunsMock
  : getAgentInstanceTaskRunsReal;

// ========================================
// AGENT DETAILS (RUNS BY CLASS NAME)
// ========================================

const getDetailsReal = async (agentName: string): Promise<AgentRun[]> => {
  const response = await axios.get(
    `${config.DATA_API}/agents/${agentName}/runs`
  );
  return response.data as AgentRun[];
};

export const getDetails = USE_MOCK_DATA ? getDetailsMock : getDetailsReal;

// ========================================
// DATASET-SPECIFIC AGENT DETAILS
// ========================================

const getDetailsForDatasetReal = async (
  datasetId: string,
  agentName: string
): Promise<AgentRun[]> => {
  const response = await axios.get(
    `${config.DATA_API}/${datasetId}/agents/${agentName}/runs`
  );
  return response.data as AgentRun[];
};

export const getDetailsForDataset = USE_MOCK_DATA
  ? getDetailsForDatasetMock
  : getDetailsForDatasetReal;

// ========================================
// RUN DETAILS API (FOR COMPARISON)
// ========================================

const getRunDetailsReal = async (
  runIds: string[]
): Promise<RunDetailsResponse[]> => {
  const runIdsParam = runIds.join(',');
  const response = await axios.get(
    `${config.DATA_API}/runs/details?run_ids=${runIdsParam}`
  );
  return response.data as RunDetailsResponse[];
};

export const getRunDetails = USE_MOCK_DATA
  ? getRunDetailsMock
  : getRunDetailsReal;

// ========================================
// TASK DETAILS API
// ========================================

const getTaskDetailsReal = async (
  runId: string,
  taskId: number
): Promise<TaskOutput> => {
  const encodedTaskId = encodeURIComponent(taskId);
  const response = await axios.get(
    `${config.DATA_API}/runs/${runId}/tasks/${encodedTaskId}/details`
  );
  return response.data as TaskOutput;
};

export const getTaskDetails = USE_MOCK_DATA
  ? getTaskDetailsMock
  : getTaskDetailsReal;

// ========================================
// OBSERVABILITY LOGS API
// ========================================

const getObservabilityLogsReal = async (
  runId: string,
  taskId: number
): Promise<Record<string, unknown>> => {
  const encodedTaskId = encodeURIComponent(String(taskId));
  const response = await axios.get(
    `${config.DATA_API}/observability/logs?run_id=${runId}&task_id=${encodedTaskId}`
  );
  return response.data.labels || {};
};

export const getObservabilityLogs = USE_MOCK_DATA
  ? getObservabilityLogsMock
  : getObservabilityLogsReal;

// ========================================
// REFRESH DATA API
// ========================================

const refreshDataReal = async (): Promise<{
  success: boolean;
  message: string;
  total_tasks: number;
  total_agents: number;
}> => {
  const response = await axios.post(`${config.DATA_API}/refresh`);
  return response.data;
};

export const refreshData = USE_MOCK_DATA ? refreshDataMock : refreshDataReal;

// ========================================
// BULK ADD TAGS API
// ========================================

export interface BulkAddTagsRequest {
  task_ids: number[]; // List of task database IDs
  tags: string[]; // Tags to add (each string is used as both key and value)
}

export interface BulkAddTagsResponse {
  success: boolean;
  message: string;
  tasks_updated: number;
  tags_added: number;
}

const bulkAddTagsReal = async (
  request: BulkAddTagsRequest
): Promise<BulkAddTagsResponse> => {
  const response = await axios.post<BulkAddTagsResponse>(
    `${config.DATA_API}/tasks/tags`,
    request
  );
  return response.data;
};

export const bulkAddTags = USE_MOCK_DATA ? bulkAddTagsMock : bulkAddTagsReal;

// ========================================
// UPLOAD TASKS YAML API
// ========================================

export interface UploadTasksYamlResponse {
  success: boolean;
  message: string;
  dataset_id: string;
  tasks_created: number;
  tasks_updated: number;
}

const uploadTasksYamlReal = async (
  file: File
): Promise<UploadTasksYamlResponse> => {
  const formData = new FormData();
  formData.append('file', file);

  const response = await axios.post<UploadTasksYamlResponse>(
    `${config.DATA_API}/ingest/tasks/yaml`,
    formData,
    {
      headers: {
        'Content-Type': 'multipart/form-data',
      },
    }
  );
  return response.data;
};

export const uploadTasksYaml = USE_MOCK_DATA
  ? uploadTasksYamlMock
  : uploadTasksYamlReal;

// ========================================
// AGENT SUMMARIES HELPER
// ========================================

export type AgentSummaryTemp = {
  agentName: string;
  totalTasks: number;
  successRate: number;
  avgTime: number;
  avgTokens: number;
  avgLlmCalls: number;
  tags?: Record<string, string>;
};

export async function fetchAgentSummaries(): Promise<AgentSummaryTemp[]> {
  const agentsRes = await getAgentClassData();
  const agents: AgentSummary[] = agentsRes;

  const summaries = await Promise.all(
    agents.map(async agent => {
      return {
        agentName: agent.cls_name,
        totalTasks: agent.best_run?.total_tasks || 0,
        successRate: agent.best_run
          ? agent.best_run.success_count / agent.best_run.total_tasks
          : 0,
        avgTime: agent.best_run ? agent.best_run.avg_cpu_time_sec : 0,
        avgTokens: agent.best_run ? agent.best_run.avg_total_tokens : 0,
        avgLlmCalls: agent.best_run
          ? agent.best_run.avg_llm_invocation_count
          : 0,
      };
    })
  );

  return summaries;
}

// ========================================
// BENCHMARKS API
// ========================================

const getBenchmarksReal = async (): Promise<Benchmark[]> => {
  const response = await axios.get(`${config.DATA_API}/datasets`);
  return response.data as Benchmark[];
};

export const getBenchmarks = USE_MOCK_DATA
  ? getBenchmarksMock
  : getBenchmarksReal;

// ========================================
// BENCHMARK AGENTS API
// ========================================

type BenchmarkAgentData = AgentSummary[];

const getBenchmarkAgentsReal = async (
  benchmarkId: string
): Promise<BenchmarkAgentData> => {
  const response = await axios.get(
    `${config.DATA_API}/${benchmarkId}/agents/classes`
  );
  return response.data as BenchmarkAgentData;
};

export const getBenchmarkAgents = USE_MOCK_DATA
  ? getBenchmarkAgentsMock
  : getBenchmarkAgentsReal;

// ========================================
// DATASET AGENT INSTANCES API
// ========================================

const getDatasetAgentInstancesReal = async (
  datasetId: string,
  agentClsChecksum: string
): Promise<AgentInstanceSummary[]> => {
  const response = await axios.get(
    `${config.DATA_API}/${datasetId}/agents/class/${agentClsChecksum}/instances`
  );
  return response.data as AgentInstanceSummary[];
};

export const getDatasetAgentInstances = USE_MOCK_DATA
  ? getDatasetAgentInstancesMock
  : getDatasetAgentInstancesReal;

// ========================================
// DATASET INSTANCE RUNS API
// ========================================

const getDatasetInstanceRunsReal = async (
  datasetId: string,
  agentChecksum: string
): Promise<AgentRun[]> => {
  const response = await axios.get(
    `${config.DATA_API}/${datasetId}/agents/instance/${agentChecksum}/runs`
  );
  return response.data as AgentRun[];
};

export const getDatasetInstanceRuns = USE_MOCK_DATA
  ? getDatasetInstanceRunsMock
  : getDatasetInstanceRunsReal;

// ========================================
// TASKSETS API
// ========================================

const getTaskSetsReal = async (): Promise<TaskSet[]> => {
  const response = await axios.get(`${config.DATA_API}/datasets`);

  const tempB: Benchmark[] = response.data;
  const tempTaskSets: TaskSet[] = tempB.map(b => ({
    id: b.dataset_id,
    name: b.dataset_id ?? '',
    description: b.description ?? '',
    created_at: b.created_at ?? '',
  }));

  return tempTaskSets;
};

export const getTaskSets = USE_MOCK_DATA ? getProjectsMock : getTaskSetsReal;

// Legacy export for backward compatibility
export const getProjects = getTaskSets;

// ========================================
// TASKSET DATASETS API
// ========================================

const getTaskSetDatasetsReal = async (
  tasksetId: string
): Promise<Benchmark[]> => {
  const response = await axios.get(
    `${config.DATA_API}/tasksets/${tasksetId}/datasets`
  );
  return response.data as Benchmark[];
};

export const getTaskSetDatasets = USE_MOCK_DATA
  ? getProjectDatasetsMock
  : getTaskSetDatasetsReal;

// Legacy export for backward compatibility
export const getProjectDatasets = getTaskSetDatasets;

// ========================================
// TASKSET RESULTS API
// ========================================

const getTaskSetResultsReal = async (
  tasksetId: string
): Promise<TaskSetResults> => {
  const response = await axios.get(
    `${config.DATA_API}/datasets/${tasksetId}/results`
  );
  return response.data as TaskSetResults;
};

export const getTaskSetResults = USE_MOCK_DATA
  ? getProjectResultsMock
  : getTaskSetResultsReal;

// Legacy export for backward compatibility
export const getProjectResults = getTaskSetResults;

// ========================================
// VISUALIZER TYPES
// ========================================

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

export async function getTraceIdsForRun(
  runId: string,
  opts?: {
    startMs?: number;
    endMs?: number;
    lookbackMinutes?: number;
    limit?: number;
  }
): Promise<VisualizerTraceIdsResponse> {
  if (USE_MOCK_DATA) return { run_id: runId, trace_ids: [], total: 0 };
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
}

export async function getParsedSpansForTrace(
  traceId: string
): Promise<VisualizerSpansResponse> {
  if (USE_MOCK_DATA) return { spans: [] };
  const url = `${config.DATA_API}/visualizer/data/tempo/traces/${encodeURIComponent(
    traceId
  )}/spans`;
  const resp = await axios.get(url);
  return resp.data as VisualizerSpansResponse;
}

export async function getLogsBySpan(args: {
  service: string;
  traceId: string;
  spanId: string;
  startMs: number;
  endMs: number;
  limit?: number;
  direction?: 'backward' | 'forward';
}): Promise<Record<string, unknown>> {
  if (USE_MOCK_DATA) return {};
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
}
