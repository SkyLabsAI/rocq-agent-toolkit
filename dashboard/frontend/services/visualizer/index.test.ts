import axios from 'axios';
import { config } from '@/config/environment';

// Mock axios
jest.mock('axios');
const mockedAxios = axios as jest.Mocked<typeof axios>;

// Mock config
const mockConfig = {
  DATA_API: 'http://localhost:8000',
  USE_MOCK_DATA: false,
};

jest.mock('@/config/environment', () => ({
  config: mockConfig,
}));

// Mock mockdata to ensure real functions are used
jest.mock('@/services/mockdata', () => ({
  getTraceIdsForRunMock: jest.fn(),
  getParsedSpansForTraceMock: jest.fn(),
  getLogsBySpanMock: jest.fn(),
}));

// We need to test the real implementations, so we'll import the module
// and manually call the internal real functions by testing through the public API
// but ensuring USE_MOCK_DATA evaluates to false
describe('visualizer service', () => {
  // Set NODE_ENV before importing the module
  const originalEnv = process.env.NODE_ENV;
  
  beforeAll(() => {
    // Temporarily set to non-test to avoid mock data
    process.env.NODE_ENV = 'production';
  });

  afterAll(() => {
    process.env.NODE_ENV = originalEnv;
  });

  beforeEach(() => {
    jest.clearAllMocks();
    // Ensure config is set correctly
    mockConfig.USE_MOCK_DATA = false;
  });

  // Helper to setup axios mock after module reset
  const setupAxiosMock = () => {
    const axios = require('axios');
    jest.spyOn(axios, 'get').mockResolvedValue({ data: {} });
    return axios;
  };

  describe('getTraceIdsForRun', () => {
    // Dynamically import to get fresh module with correct environment
    it('should build URL with default lookback minutes and limit', async () => {
      // Clear module cache and re-import
      jest.resetModules();
      const axios = setupAxiosMock();
      
      const { getTraceIdsForRun } = await import('./index');
      
      const mockResponse = {
        run_id: 'run1',
        trace_ids: ['trace1', 'trace2'],
        total: 2,
      };

      const axiosMock = require('axios');
      axios.get.mockResolvedValueOnce({ data: mockResponse });

      await getTraceIdsForRun('run1');

      expect(axios.get).toHaveBeenCalled();
      const callUrl = axios.get.mock.calls[0][0] as string;
      expect(callUrl).toContain('/visualizer/data/runs/run1/trace-ids');
      expect(callUrl).toMatch(/lookback_minutes=15/);
      expect(callUrl).toMatch(/limit=25/);
    });

    it('should build URL with custom lookback minutes and limit', async () => {
      jest.resetModules();
      const axios = setupAxiosMock();
      
      const { getTraceIdsForRun } = await import('./index');
      
      const mockResponse = {
        run_id: 'run1',
        trace_ids: [],
        total: 0,
      };

      axios.get.mockResolvedValueOnce({ data: mockResponse });

      await getTraceIdsForRun('run1', {
        lookbackMinutes: 30,
        limit: 50,
      });

      const callUrl = axios.get.mock.calls[0][0] as string;
      expect(callUrl).toMatch(/lookback_minutes=30/);
      expect(callUrl).toMatch(/limit=50/);
    });

    it('should use startMs and endMs when provided', async () => {
      jest.resetModules();
      const axios = setupAxiosMock();
      
      const { getTraceIdsForRun } = await import('./index');
      
      const mockResponse = {
        run_id: 'run1',
        trace_ids: [],
        total: 0,
      };

      axios.get.mockResolvedValueOnce({ data: mockResponse });

      await getTraceIdsForRun('run1', {
        startMs: 1000,
        endMs: 2000,
      });

      const callUrl = axios.get.mock.calls[0][0] as string;
      expect(callUrl).toMatch(/start_ms=1000/);
      expect(callUrl).toMatch(/end_ms=2000/);
      expect(callUrl).not.toMatch(/lookback_minutes/);
    });

    it('should encode run ID in URL', async () => {
      jest.resetModules();
      const axios = setupAxiosMock();
      
      const { getTraceIdsForRun } = await import('./index');
      
      const mockResponse = {
        run_id: 'run/with/slashes',
        trace_ids: [],
        total: 0,
      };

      axios.get.mockResolvedValueOnce({ data: mockResponse });

      await getTraceIdsForRun('run/with/slashes');

      const callUrl = axios.get.mock.calls[0][0] as string;
      expect(callUrl).toContain('run%2Fwith%2Fslashes');
    });

    it('should return response data', async () => {
      jest.resetModules();
      const axios = setupAxiosMock();
      
      const { getTraceIdsForRun } = await import('./index');
      
      const mockResponse = {
        run_id: 'run1',
        trace_ids: ['trace1', 'trace2'],
        total: 2,
      };

      axios.get.mockResolvedValueOnce({ data: mockResponse });

      const result = await getTraceIdsForRun('run1');

      expect(result).toEqual(mockResponse);
    });
  });

  describe('getParsedSpansForTrace', () => {
    it('should build correct URL for trace', async () => {
      jest.resetModules();
      const axios = setupAxiosMock();
      
      const { getParsedSpansForTrace } = await import('./index');
      
      const mockResponse = {
        spans: [],
      };

      axios.get.mockResolvedValueOnce({ data: mockResponse });

      await getParsedSpansForTrace('trace1');

      expect(axios.get).toHaveBeenCalledWith(
        'http://localhost:8000/visualizer/data/tempo/traces/trace1/spans'
      );
    });

    it('should encode trace ID in URL', async () => {
      jest.resetModules();
      const axios = setupAxiosMock();
      
      const { getParsedSpansForTrace } = await import('./index');
      
      const mockResponse = {
        spans: [],
      };

      axios.get.mockResolvedValueOnce({ data: mockResponse });

      await getParsedSpansForTrace('trace/with/special-chars');

      expect(axios.get).toHaveBeenCalledWith(
        expect.stringContaining('trace%2Fwith%2Fspecial-chars')
      );
    });

    it('should return response data', async () => {
      jest.resetModules();
      const axios = setupAxiosMock();
      
      const { getParsedSpansForTrace } = await import('./index');
      
      const mockResponse = {
        spans: [
          {
            trace_id: 'trace1',
            span_id: 'span1',
            name: 'span',
            service_name: 'service1',
          },
        ],
      };

      axios.get.mockResolvedValueOnce({ data: mockResponse });

      const result = await getParsedSpansForTrace('trace1');

      expect(result).toEqual(mockResponse);
    });
  });

  describe('getLogsBySpan', () => {
    it('should build URL with all required parameters', async () => {
      jest.resetModules();
      const axios = setupAxiosMock();
      
      const { getLogsBySpan } = await import('./index');
      
      const mockResponse = {};

      axios.get.mockResolvedValueOnce({ data: mockResponse });

      await getLogsBySpan({
        service: 'service1',
        traceId: 'trace1',
        spanId: 'span1',
        startMs: 1000,
        endMs: 2000,
      });

      const callUrl = axios.get.mock.calls[0][0] as string;
      const url = new URL(callUrl);

      expect(url.pathname).toBe('/visualizer/data/logs/by-span');
      expect(url.searchParams.get('service')).toBe('service1');
      expect(url.searchParams.get('trace_id')).toBe('trace1');
      expect(url.searchParams.get('span_id')).toBe('span1');
      expect(url.searchParams.get('start_ms')).toBe('1000');
      expect(url.searchParams.get('end_ms')).toBe('2000');
    });

    it('should use default limit and direction', async () => {
      jest.resetModules();
      const axios = setupAxiosMock();
      
      const { getLogsBySpan } = await import('./index');
      
      const mockResponse = {};

      axios.get.mockResolvedValueOnce({ data: mockResponse });

      await getLogsBySpan({
        service: 'service1',
        traceId: 'trace1',
        spanId: 'span1',
        startMs: 1000,
        endMs: 2000,
      });

      const callUrl = axios.get.mock.calls[0][0] as string;
      const url = new URL(callUrl);

      expect(url.searchParams.get('limit')).toBe('200');
      expect(url.searchParams.get('direction')).toBe('backward');
    });

    it('should use custom limit and direction', async () => {
      jest.resetModules();
      const axios = setupAxiosMock();
      
      const { getLogsBySpan } = await import('./index');
      
      const mockResponse = {};

      axios.get.mockResolvedValueOnce({ data: mockResponse });

      await getLogsBySpan({
        service: 'service1',
        traceId: 'trace1',
        spanId: 'span1',
        startMs: 1000,
        endMs: 2000,
        limit: 500,
        direction: 'forward',
      });

      const callUrl = axios.get.mock.calls[0][0] as string;
      const url = new URL(callUrl);

      expect(url.searchParams.get('limit')).toBe('500');
      expect(url.searchParams.get('direction')).toBe('forward');
    });

    it('should encode special characters in query params', async () => {
      jest.resetModules();
      const axios = setupAxiosMock();
      
      const { getLogsBySpan } = await import('./index');
      
      const mockResponse = {};

      axios.get.mockResolvedValueOnce({ data: mockResponse });

      await getLogsBySpan({
        service: 'service/with/slashes',
        traceId: 'trace with spaces',
        spanId: 'span&id=value',
        startMs: 1000,
        endMs: 2000,
      });

      const callUrl = axios.get.mock.calls[0][0] as string;
      const url = new URL(callUrl);

      expect(url.searchParams.get('service')).toBe('service/with/slashes');
      expect(url.searchParams.get('trace_id')).toBe('trace with spaces');
      expect(url.searchParams.get('span_id')).toBe('span&id=value');
    });

    it('should return response data', async () => {
      jest.resetModules();
      const axios = setupAxiosMock();
      
      const { getLogsBySpan } = await import('./index');
      
      const mockResponse = {
        logs: ['log1', 'log2'],
      };

      axios.get.mockResolvedValueOnce({ data: mockResponse });

      const result = await getLogsBySpan({
        service: 'service1',
        traceId: 'trace1',
        spanId: 'span1',
        startMs: 1000,
        endMs: 2000,
      });

      expect(result).toEqual(mockResponse);
    });
  });
});
