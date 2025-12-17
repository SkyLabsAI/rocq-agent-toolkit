# Test Failures Analysis

## Summary
- **Total Tests**: 358
- **Passing**: 311 (86.9%)
- **Failing**: 47 (13.1%)

## Issues by Category

### 1. **TEST ISSUES** (Tests are wrong, code is correct)

#### `hooks/use-dataview.test.ts`
**Problem**: Tests expect `fetchAgentsForBenchmark` and `benchmarkAgents` but `useBenchmarks` hook doesn't return these.
- **Test expects**: `result.current.fetchAgentsForBenchmark('bench1')` and `result.current.benchmarkAgents.get('bench1')`
- **Hook actually returns**: `{ benchmarks, loading, error, refetch }`
- **Fix**: Update tests to use `useBenchmarkAgents` hook instead, or remove these tests if functionality doesn't exist.

#### `components/RunDetailsView.test.tsx`
**Problem**: Test uses `getByText('1')` which matches multiple elements (success count, failure count, etc.)
- **Fix**: Use more specific queries like `getByText('1', { selector: '.text-text-success' })` or `getAllByText('1')[0]`

#### `components/base/tacticInfo/index.test.tsx`
**Problem**: Multiple tactics render the same text, causing "Found multiple elements" errors
- **Fix**: Use `getAllByText()` and index, or add `data-testid` attributes, or use more specific queries

#### `components/base/comparisonModal/hooks/useComparisonLogs.test.ts`
**Problem**: Mock is called too many times (46 instead of 2, 24 instead of 1)
- **Issue**: Hook might be re-rendering or effect dependencies causing multiple calls
- **Fix**: Add proper cleanup in tests, or adjust expectations if multiple calls are expected

### 2. **CODE ISSUES** (Code needs fixing)

#### `hooks/useAgentsSummary.test.ts` - "should close modal"
**Problem**: `closeModal()` doesn't properly close the modal
- **Expected**: `modalState.isOpen` should be `false` after `closeModal()`
- **Received**: `modalState.isOpen` is still `true`
- **Code location**: `hooks/useAgentsSummary.ts` lines 69-75
- **Fix needed**: Check if `closeModal` is actually being called or if there's a state update issue. The code looks correct, might be a timing issue - test needs `waitFor` or `act()` wrapper.

### 3. **MOCK/SETUP ISSUES** (Test setup problems)

#### `components/base/comparisonModal/index.test.tsx`
**Problem**: Tab switching and content rendering not working in tests
- **Issue**: Mocks might not be set up correctly for the modal's internal state
- **Fix**: Ensure mocks properly simulate the hook's behavior

#### `features/localdashboard/AgentRunsView.test.tsx`
**Problem**: Multiple test failures related to rendering
- **Issue**: Mock setup for components/hooks might be incomplete
- **Fix**: Review and fix mocks for `useSelectedRun`, `RunRow`, `StickyCompareBar`

#### `features/localdashboard/dataview/data-item/index.test.tsx`
**Problem**: "should show RunDetailsView when run is selected" failing
- **Issue**: Conditional rendering logic not being triggered in test
- **Fix**: Ensure `selectedRun` is properly set in mock

#### `features/agents-compare/agent-compare-content.test.tsx`
**Problem**: "should show loading state initially" failing
- **Issue**: Loading state not being properly simulated
- **Fix**: Check mock setup for `useAgents` hook

### 4. **ASYNC/TIMING ISSUES** (Tests need better async handling)

#### `components/base/comparisonModal/hooks/useComparisonLogs.test.ts` - "should handle general error"
**Problem**: Error state not being set correctly
- **Expected**: `error` should be "Failed to load comparison data"
- **Received**: `error` is `null`
- **Fix**: Check error handling in hook, might need `waitFor` in test

#### Multiple component tests
**Problem**: State updates not being awaited properly
- **Fix**: Wrap state updates in `act()` or use `waitFor()` for async state changes

## Recommended Fix Priority

### High Priority (Easy fixes - test issues)
1. ✅ Fix `use-dataview.test.ts` - Remove or fix tests for non-existent functionality
2. ✅ Fix `RunDetailsView.test.tsx` - Use more specific queries
3. ✅ Fix `tacticInfo/index.test.tsx` - Use `getAllByText()` or add test IDs

### Medium Priority (Code/timing issues)
4. ⚠️ Fix `useAgentsSummary.test.ts` - Add proper async handling for `closeModal`
5. ⚠️ Fix `useComparisonLogs.test.ts` - Fix error handling or test expectations

### Low Priority (Mock/setup issues)
6. 🔧 Fix remaining component test mocks and setup issues

## Quick Wins

Most failures are **test issues** rather than code bugs:
- Tests expecting functionality that doesn't exist
- Tests using non-specific queries that match multiple elements
- Tests not properly handling async state updates

The actual application code appears to be mostly correct based on the test failures.

