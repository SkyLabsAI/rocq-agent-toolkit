/**
 * Mock Data Service
 *
 * This module provides mock data for testing and development.
 * All mock functions simulate realistic API responses with appropriate delays.
 */

// Agent-related mocks
export {
  getAgentClassDataMock,
  getAgentInstancesMock,
  getDatasetAgentInstancesMock,
  getDetailsMock,
} from './agents';

// Run-related mocks
export {
  getDatasetInstanceRunsMock,
  getDetailsForDatasetMock,
  getObservabilityLogsMock,
  getRunDetailsMock,
  getRunsByInstanceMock,
  refreshDataMock,
} from './runs';

// Benchmark-related mocks
export { getBenchmarkAgentsMock, getBenchmarksMock } from './benchmarks';

// Visualizer-related mocks (NEW!)
export {
  getLogsBySpanMock,
  getParsedSpansForTraceMock,
  getTraceIdsForRunMock,
} from './visualizer';

// Helper generators
export {
  generateHexString,
  generateMockTaskOutput,
  generateTimestampInRange,
  simulateDelay,
} from './generators';
