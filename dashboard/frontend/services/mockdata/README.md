# Mock Data Service

This directory contains organized mock data for testing and development purposes.

## Structure

```
mockdata/
├── index.ts              # Main export file
├── generators.ts         # Helper functions for generating mock data
├── agents.ts            # Agent-related mock data
├── runs.ts              # Run-related mock data
├── benchmarks.ts        # Benchmark/dataset mock data
├── visualizer.ts        # Visualizer mock data (NEW!)
└── README.md            # This file
```

## Files

### `generators.ts`
Contains helper functions for generating consistent mock data:
- `generateMockTaskOutput()` - Creates realistic task outputs
- `generateHexString()` - Generates random hex strings (for IDs)
- `generateTimestampInRange()` - Creates timestamps within a range
- `simulateDelay()` - Simulates network delays

### `agents.ts`
Mock data for agent-related API endpoints:
- `getAgentClassDataMock()` - Returns mock agent class summaries
- `getAgentInstancesMock()` - Returns mock agent instances
- `getDatasetAgentInstancesMock()` - Returns mock dataset-specific instances
- `getDetailsMock()` - Returns mock agent runs

### `runs.ts`
Mock data for run-related API endpoints:
- `getRunsByInstanceMock()` - Returns mock runs by instance
- `getDetailsForDatasetMock()` - Returns mock dataset-specific runs
- `getDatasetInstanceRunsMock()` - Returns mock dataset instance runs
- `getRunDetailsMock()` - Returns detailed run information for comparison
- `getObservabilityLogsMock()` - Returns mock observability logs (tactics, proofs, etc.)
- `refreshDataMock()` - Simulates data refresh operation

### `benchmarks.ts`
Mock data for benchmark/dataset API endpoints:
- `getBenchmarksMock()` - Returns mock benchmark list
- `getBenchmarkAgentsMock()` - Returns mock agents for a specific benchmark

### `visualizer.ts` ⭐ NEW!
Mock data for visualizer API endpoints with **realistic trace and span data**:
- `getTraceIdsForRunMock()` - Returns 5-15 mock trace IDs per run
- `getParsedSpansForTraceMock()` - Returns hierarchical span tree with:
  - Root span (agent.execute)
  - Child operations (llm.inference, coq.compile, tactic.apply, etc.)
  - Nested spans (tokenization, forward pass, decoding)
  - Realistic timestamps and durations
  - Proper parent-child relationships
  - Rich attributes for each span
- `getLogsBySpanMock()` - Returns 5-20 mock log entries per span with:
  - Timestamps
  - Log levels (DEBUG, INFO, WARN, ERROR)
  - Structured log messages
  - Service and span metadata

## Usage

Import mock functions from the main index file:

```typescript
import {
  getAgentClassDataMock,
  getRunDetailsMock,
  getTraceIdsForRunMock,
  // ... other mocks
} from '@/services/mockdata';
```

## Configuration

Mock data is automatically used when `USE_MOCK_DATA` is true in the environment configuration:

```typescript
// config/environment/index.ts
export const config = {
  USE_MOCK_DATA: process.env.USE_MOCK_DATA === 'true',
  // ...
};
```

## Testing with Playwright

The mock data is designed to work seamlessly with Playwright tests. See `e2e/visualizer.spec.ts` for comprehensive examples of testing the visualizer with mock data.

### Running Playwright Tests

```bash
# Run all tests
pnpm playwright test

# Run visualizer tests only
pnpm playwright test visualizer

# Run tests with UI
pnpm playwright test --ui

# Generate tests with codegen
pnpm playwright codegen http://localhost:3000
```

## Mock Data Characteristics

- **Realistic Delays**: All mock functions include simulated network delays (200-1500ms)
- **Consistent Structure**: Mock data follows the same type definitions as real API responses
- **Variability**: Random elements ensure diverse test scenarios
- **Console Logging**: Mock functions log their responses for debugging
- **Rich Data**: Includes nested objects, arrays, and complex relationships

## Visualizer Mock Data Details

The visualizer mock data is particularly comprehensive:

### Trace Structure
- 5-15 traces per run
- 32-character hex trace IDs
- Realistic timestamp ranges

### Span Hierarchy
```
agent.execute (root)
├── llm.inference
│   ├── llm.tokenize
│   ├── llm.forward_pass
│   └── llm.decode
├── coq.compile
├── tactic.apply
├── proof.validate
└── cache.lookup
```

### Span Attributes
Each span includes:
- Service name (rocq-agent, llm-service, coq-service, etc.)
- Start and end timestamps (nanoseconds)
- Parent-child relationships
- Rich metadata (model names, token counts, proof status, etc.)

### Log Entries
Each span can have 5-20 log entries with:
- Structured format (timestamp, level, message)
- Multiple log levels
- Service and trace context
- Searchable content

## Future Enhancements

Potential improvements for the mock data:
- Add more diverse failure scenarios
- Include edge cases (empty data, malformed responses)
- Add mock data versioning
- Create custom mock data builders for specific test scenarios
- Add performance profiling data

## Contributing

When adding new mock data:
1. Create mock functions in the appropriate file
2. Export them from `index.ts`
3. Add corresponding real API functions in the service files
4. Update this README with documentation
5. Add Playwright tests to verify the mock data works correctly

