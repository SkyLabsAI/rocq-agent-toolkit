# E2E Test Documentation

## Test Structure Overview

This document describes the comprehensive E2E test suite that covers the new hierarchical flow structure of the RAT Dashboard application.

## Application Flow Structure

### Agent View
```
Agents → Datasets → Runs
```
- **Level 1**: List of agents with sorting capabilities
- **Level 2**: Each agent shows datasets they have runs in
- **Level 3**: Each agent-dataset combination shows runs for that specific combination

### Dataset View  
```
Datasets → Agents → Runs
```
- **Level 1**: List of datasets
- **Level 2**: Each dataset shows agents that have runs in it
- **Level 3**: Each dataset-agent combination shows runs for that specific combination

## Comparison Rules

### Agent Comparison
- Multiple agents can be compared within the same dataset
- Selecting agents from different datasets clears previous selections
- Navigate to `/compare/agents?agents=agentA,agentB` using memory router only

### Run Comparison  
- Multiple runs can be compared within the same dataset
- Runs must belong to the same dataset to be comparable
- Navigate to `/compare?runs=run1,run2` using memory router only

### Selection Clearing Behavior
- Opening a comparison on another dataset automatically clears selections from the first dataset
- This prevents invalid cross-dataset comparisons
- Sticky compare bar disappears when selections are cleared

## Test Files

### 1. `agent-view.spec.ts`
Tests the agent-first hierarchy flow:
- Agent list display and sorting
- Agent expansion to show datasets
- Dataset expansion to show runs
- Run selection within same dataset
- Selection clearing when switching datasets
- Full user flow video recording

### 2. `dataset-view.spec.ts`  
Tests the dataset-first hierarchy flow:
- Dataset list display
- Dataset expansion to show agents
- Agent expansion to show runs
- Agent comparison within same dataset
- Run comparison within same dataset
- Navigation to comparison pages
- Selection clearing behavior

### 3. `comparison-flows.spec.ts`
Tests comparison workflows:
- Agent comparison from dataset view
- Run comparison from dataset view
- Cross-dataset selection prevention
- Navigation back from comparison pages
- Sticky compare bar behavior

### 4. `navigation.spec.ts`
Tests routing and navigation:
- View switching (agent ↔ dataset)
- Direct URL navigation to comparison pages
- 404 handling
- State maintenance during navigation

### 5. `home.spec.ts`
Tests homepage and dashboard:
- Initial page load
- View switcher controls
- Theme switching
- Content display based on selected view

## Screenshots and Videos

### Screenshot Organization
```
test-results/screenshots/
├── agent-view/
│   ├── agent-list-initial.png
│   ├── agent-expanded-datasets.png
│   ├── agent-dataset-expanded-runs.png
│   └── agent-runs-selected-same-dataset.png
├── dataset-view/
│   ├── dataset-list-initial.png
│   ├── dataset-expanded-agents.png
│   ├── dataset-agent-expanded-runs.png
│   └── dataset-agents-selected-same-dataset.png
├── comparison-flows/
│   ├── agent-comparison-start.png
│   ├── agents-selected-for-comparison.png
│   └── agent-comparison-results.png
└── navigation/
    ├── homepage.png
    ├── dataset-view.png
    └── agent-view.png
```

### Video Recording
- Full user flows are recorded as `.webm` files
- Videos show complete interactions from start to finish
- Stored in `test-results/videos/`

## Test Utilities (`test-helpers.ts`)

### Core Functions
- `waitForPageLoad()` - Ensures complete page loading
- `takeScreenshot()` - Organized screenshot capture
- `switchToView()` - Switch between agent/dataset views
- `selectMultipleItems()` - Select items via checkboxes

### Flow Functions
- `completeAgentViewFlow()` - Complete agent → dataset → runs flow
- `completeDatasetViewFlow()` - Complete dataset → agent → runs flow
- `testDatasetSwitchingClearsSelections()` - Verify selection clearing

### Verification Functions
- `verifyStickyCompareBar()` - Check sticky compare bar visibility
- `verifyNoSelections()` - Ensure no items are selected
- `navigateToAgentComparison()` - Navigate to agent comparison
- `navigateToRunComparison()` - Navigate to run comparison

## Configuration

### Playwright Configuration
- Screenshot capture: `on` (captures all test screenshots)
- Video recording: `on` (records all test videos)
- Viewport: 1280x720 for consistent screenshot sizing
- Base URL: `http://localhost:3000`

### Test Data Requirements
- Mock data should include multiple agents
- Mock data should include multiple datasets
- Each agent should have runs in multiple datasets
- Each dataset should have multiple agents

## Running Tests

### Full Test Suite
```bash
npx playwright test
```

### Specific Test Files
```bash
npx playwright test agent-view.spec.ts
npx playwright test dataset-view.spec.ts
npx playwright test comparison-flows.spec.ts
```

### With UI Mode (for debugging)
```bash
npx playwright test --ui
```

### Generate Report
```bash
npx playwright show-report
```

## Expected Test Outcomes

### Success Criteria
1. All hierarchical navigation flows work correctly
2. Selection behavior follows dataset isolation rules
3. Comparison pages load with correct data
4. Cross-dataset selections are prevented
5. UI state is maintained appropriately
6. Screenshots document each step of user flows
7. Videos capture complete interaction sequences

### Performance Expectations
- Page loads complete within 10 seconds
- UI interactions respond within 1 second
- No critical console errors during flows
- Smooth transitions between states

## Troubleshooting

### Common Issues
1. **Mock data not loading**: Verify `NEXT_PUBLIC_USE_MOCK_DATA=true`
2. **Selectors not found**: Check component test IDs and class names
3. **Timing issues**: Increase wait timeouts if needed
4. **Screenshot failures**: Ensure test-results directory exists

### Debug Tips
- Use `--headed` flag to see browser during tests
- Add `await page.pause()` for interactive debugging
- Check network tab for API call failures
- Verify component rendering with browser dev tools