import axios from 'axios';
import {
  fetchAgentSummaries,
  getAgentInstanceTaskRuns,
  getTaskSets,
  bulkAddTags,
  type BulkAddTagsRequest,
  type BulkAddTagsResponse,
} from './index';
import { config } from '@/config/environment';
import type {
  AgentSummary,
  AgentRun,
  Benchmark,
  RunDetailsResponse,
} from '@/types/types';

// Mock axios
jest.mock('axios');
const mockedAxios = axios as jest.Mocked<typeof axios>;

// Mock config - ensure USE_MOCK_DATA is false for testing real implementations
jest.mock('@/config/environment', () => ({
  config: {
    DATA_API: 'http://localhost:8000',
    USE_MOCK_DATA: false,
  },
}));

describe('dataservice', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  describe('fetchAgentSummaries', () => {
    it('should calculate agent summaries correctly', async () => {
      const mockAgents: AgentSummary[] = [
        {
          cls_name: 'Agent1',
          cls_checksum: 'checksum1',
          best_run: {
            run_id: 'run1',
            agent_name: 'Agent1',
            timestamp_utc: '2024-01-01T00:00:00Z',
            total_tasks: 10,
            success_count: 8,
            failure_count: 2,
            avg_cpu_time_sec: 5.5,
            avg_total_tokens: 1000,
            avg_llm_invocation_count: 3,
          },
        },
        {
          cls_name: 'Agent2',
          cls_checksum: 'checksum2',
          best_run: {
            run_id: 'run2',
            agent_name: 'Agent2',
            timestamp_utc: '2024-01-01T00:00:00Z',
            total_tasks: 20,
            success_count: 18,
            failure_count: 2,
            avg_cpu_time_sec: 10.0,
            avg_total_tokens: 2000,
            avg_llm_invocation_count: 5,
          },
        },
      ];

      mockedAxios.get.mockResolvedValueOnce({ data: mockAgents });

      const summaries = await fetchAgentSummaries();

      expect(summaries).toHaveLength(2);
      expect(summaries[0]).toEqual({
        agentName: 'Agent1',
        totalTasks: 10,
        successRate: 0.8,
        avgTime: 5.5,
        avgTokens: 1000,
        avgLlmCalls: 3,
      });
      expect(summaries[1]).toEqual({
        agentName: 'Agent2',
        totalTasks: 20,
        successRate: 0.9,
        avgTime: 10.0,
        avgTokens: 2000,
        avgLlmCalls: 5,
      });
    });

    it('should handle agents without best_run', async () => {
      const mockAgents: AgentSummary[] = [
        {
          cls_name: 'Agent1',
          cls_checksum: 'checksum1',
        },
      ];

      mockedAxios.get.mockResolvedValueOnce({ data: mockAgents });

      const summaries = await fetchAgentSummaries();

      expect(summaries).toHaveLength(1);
      expect(summaries[0]).toEqual({
        agentName: 'Agent1',
        totalTasks: 0,
        successRate: 0,
        avgTime: 0,
        avgTokens: 0,
        avgLlmCalls: 0,
      });
    });

    it('should handle empty agent list', async () => {
      mockedAxios.get.mockResolvedValueOnce({ data: [] });

      const summaries = await fetchAgentSummaries();

      expect(summaries).toHaveLength(0);
    });
  });

  describe('getAgentInstanceTaskRunsReal', () => {
    it('should convert run details to agent runs correctly', async () => {
      const mockTaskRunsResponse = {
        agent_checksum: 'checksum1',
        task_id: 1,
        task_name: 'Task1',
        run_ids: ['run1', 'run2'],
        total_runs: 2,
      };

      const mockRunDetails: RunDetailsResponse[] = [
        {
          run_id: 'run1',
          agent_name: 'Agent1',
          total_tasks: 3,
          tasks: [
            {
              run_id: 'run1',
              task_id: 1,
              task_name: 'Task1',
              task_kind: 'OtherTask',
              status: 'Success',
              timestamp_utc: '2024-01-01T00:00:00Z',
              agent_name: 'Agent1',
              metrics: {
                llm_invocation_count: 1,
                token_counts: {
                  input_tokens: 100,
                  output_tokens: 50,
                  total_tokens: 150,
                },
                resource_usage: {
                  execution_time_sec: 1.0,
                  cpu_time_sec: 1.0,
                  gpu_time_sec: 0,
                },
                custom: null,
              },
              results: null,
            },
            {
              run_id: 'run1',
              task_id: 2,
              task_name: 'Task2',
              task_kind: 'OtherTask',
              status: 'Success',
              timestamp_utc: '2024-01-01T00:01:00Z',
              agent_name: 'Agent1',
              metrics: {
                llm_invocation_count: 1,
                token_counts: {
                  input_tokens: 100,
                  output_tokens: 50,
                  total_tokens: 150,
                },
                resource_usage: {
                  execution_time_sec: 1.0,
                  cpu_time_sec: 1.0,
                  gpu_time_sec: 0,
                },
                custom: null,
              },
              results: null,
            },
            {
              run_id: 'run1',
              task_id: 3,
              task_name: 'Task3',
              task_kind: 'OtherTask',
              status: 'Failure',
              timestamp_utc: '2024-01-01T00:02:00Z',
              agent_name: 'Agent1',
              metrics: {
                llm_invocation_count: 1,
                token_counts: {
                  input_tokens: 100,
                  output_tokens: 50,
                  total_tokens: 150,
                },
                resource_usage: {
                  execution_time_sec: 1.0,
                  cpu_time_sec: 1.0,
                  gpu_time_sec: 0,
                },
                custom: null,
              },
              results: null,
            },
          ],
          metadata: {
            tags: { env: 'test' },
          },
        },
        {
          run_id: 'run2',
          agent_name: 'Agent1',
          total_tasks: 1,
          tasks: [
            {
              run_id: 'run2',
              task_id: 1,
              task_name: 'Task1',
              task_kind: 'OtherTask',
              status: 'Success',
              timestamp_utc: '2024-01-01T00:03:00Z',
              agent_name: 'Agent1',
              metrics: {
                llm_invocation_count: 1,
                token_counts: {
                  input_tokens: 100,
                  output_tokens: 50,
                  total_tokens: 150,
                },
                resource_usage: {
                  execution_time_sec: 1.0,
                  cpu_time_sec: 1.0,
                  gpu_time_sec: 0,
                },
                custom: null,
              },
              results: null,
            },
          ],
        },
      ];

      mockedAxios.get
        .mockResolvedValueOnce({ data: mockTaskRunsResponse })
        .mockResolvedValueOnce({ data: mockRunDetails });

      const result = await getAgentInstanceTaskRuns('checksum1', 1);

      expect(result).toHaveLength(2);
      expect(result[0]).toEqual({
        run_id: 'run1',
        agent_name: 'Agent1',
        timestamp_utc: '2024-01-01T00:00:00Z',
        total_tasks: 3,
        success_count: 2,
        failure_count: 1,
        dataset_id: '',
        metadata: {
          tags: { env: 'test' },
        },
      });
      expect(result[1]).toEqual({
        run_id: 'run2',
        agent_name: 'Agent1',
        timestamp_utc: '2024-01-01T00:03:00Z',
        total_tasks: 1,
        success_count: 1,
        failure_count: 0,
        dataset_id: '',
        metadata: {
          tags: {},
        },
      });
    });

    it('should return empty array when no run_ids', async () => {
      const mockTaskRunsResponse = {
        agent_checksum: 'checksum1',
        task_id: 1,
        task_name: 'Task1',
        run_ids: [],
        total_runs: 0,
      };

      mockedAxios.get.mockResolvedValueOnce({ data: mockTaskRunsResponse });

      const result = await getAgentInstanceTaskRuns('checksum1', 1);

      expect(result).toEqual([]);
      expect(mockedAxios.get).toHaveBeenCalledTimes(1);
    });

    it('should handle runs without tasks', async () => {
      const mockTaskRunsResponse = {
        agent_checksum: 'checksum1',
        task_id: 1,
        task_name: 'Task1',
        run_ids: ['run1'],
        total_runs: 1,
      };

      const mockRunDetails: RunDetailsResponse[] = [
        {
          run_id: 'run1',
          agent_name: 'Agent1',
          total_tasks: 0,
          tasks: [],
        },
      ];

      mockedAxios.get
        .mockResolvedValueOnce({ data: mockTaskRunsResponse })
        .mockResolvedValueOnce({ data: mockRunDetails });

      const result = await getAgentInstanceTaskRuns('checksum1', 1);

      expect(result).toHaveLength(1);
      expect(result[0].timestamp_utc).toBeDefined();
      expect(result[0].total_tasks).toBe(0);
      expect(result[0].success_count).toBe(0);
      expect(result[0].failure_count).toBe(0);
    });

    it('should encode task ID in URL', async () => {
      const mockTaskRunsResponse = {
        agent_checksum: 'checksum1',
        task_id: 123,
        task_name: 'Task1',
        run_ids: [],
        total_runs: 0,
      };

      mockedAxios.get.mockResolvedValueOnce({ data: mockTaskRunsResponse });

      await getAgentInstanceTaskRuns('checksum1', 123);

      expect(mockedAxios.get).toHaveBeenCalledWith(
        expect.stringContaining('/tasks/123/')
      );
    });
  });

  describe('getTaskSetsReal', () => {
    it('should convert benchmarks to task sets correctly', async () => {
      const mockBenchmarks: Benchmark[] = [
        {
          dataset_id: 'dataset1',
          description: 'Description 1',
          created_at: '2024-01-01T00:00:00Z',
        },
        {
          dataset_id: 'dataset2',
          description: 'Description 2',
          created_at: '2024-01-02T00:00:00Z',
        },
      ];

      mockedAxios.get.mockResolvedValueOnce({ data: mockBenchmarks });

      const result = await getTaskSets();

      expect(result).toHaveLength(2);
      expect(result[0]).toEqual({
        id: 'dataset1',
        name: 'dataset1',
        description: 'Description 1',
        created_at: '2024-01-01T00:00:00Z',
      });
      expect(result[1]).toEqual({
        id: 'dataset2',
        name: 'dataset2',
        description: 'Description 2',
        created_at: '2024-01-02T00:00:00Z',
      });
    });

    it('should handle benchmarks with missing fields', async () => {
      const mockBenchmarks: Benchmark[] = [
        {
          dataset_id: undefined,
          description: undefined,
          created_at: undefined,
        },
      ];

      mockedAxios.get.mockResolvedValueOnce({ data: mockBenchmarks });

      const result = await getTaskSets();

      expect(result).toHaveLength(1);
      expect(result[0]).toEqual({
        id: undefined,
        name: '',
        description: '',
        created_at: '',
      });
    });

    it('should handle empty benchmark list', async () => {
      mockedAxios.get.mockResolvedValueOnce({ data: [] });

      const result = await getTaskSets();

      expect(result).toEqual([]);
    });
  });

  describe('bulkAddTagsReal', () => {
    it('should call bulk add tags endpoint correctly', async () => {
      const request: BulkAddTagsRequest = {
        task_ids: [1, 2, 3],
        tags: ['tag1', 'tag2'],
      };

      const mockResponse: BulkAddTagsResponse = {
        success: true,
        message: 'Tags added successfully',
        tasks_updated: 3,
        tags_added: 2,
      };

      mockedAxios.post.mockResolvedValueOnce({ data: mockResponse });

      const result = await bulkAddTags(request);

      expect(mockedAxios.post).toHaveBeenCalledWith(
        `${config.DATA_API}/tasks/tags`,
        request
      );
      expect(result).toEqual(mockResponse);
    });
  });
});
