# Playwright Test Structure Documentation

## Overview

This comprehensive Playwright testing framework provides robust testing capabilities for the Rocq Agent Toolkit frontend application. The framework follows modern testing best practices with Page Object Model patterns, API mocking, and comprehensive test coverage.

## Directory Structure

```
tests/
├── fixtures/
│   └── index.ts              # Centralized test fixtures and mock data
├── pages/
│   ├── HomePage.ts           # Page Object Model for dashboard
│   └── TaskDetailsModal.ts   # Page Object Model for task modals
├── utils/
│   ├── apiMocker.ts         # API mocking utilities
│   └── testHelpers.ts       # Common test utilities and helpers
├── dashboard/
│   └── dashboard.spec.ts     # Dashboard functionality tests
├── taskModal/
│   └── taskModal.spec.ts     # Task modal interaction tests
├── integration/
│   └── userJourneys.spec.ts  # End-to-end user journey tests
└── accessibility/
    └── accessibility.a11y.spec.ts # Accessibility compliance tests
```

## Test Categories

### 1. Dashboard Tests (`dashboard/dashboard.spec.ts`)
- **Purpose**: Validates core dashboard functionality
- **Coverage**: 
  - Agent list rendering and interactions
  - Status filtering and data validation
  - Performance metrics display
  - Real-time updates and error handling

### 2. Task Modal Tests (`taskModal/taskModal.spec.ts`)
- **Purpose**: Tests task details modal interactions
- **Coverage**:
  - Modal opening and closing behaviors
  - Tab navigation and content verification
  - C++ code display formatting
  - Task status and metadata presentation

### 3. Integration Tests (`integration/userJourneys.spec.ts`)
- **Purpose**: End-to-end user workflow validation
- **Coverage**:
  - Complete user journeys from dashboard to task details
  - Cross-component interactions
  - Data flow validation
  - Performance and error scenarios

### 4. Accessibility Tests (`accessibility/accessibility.a11y.spec.ts`)
- **Purpose**: Ensures WCAG compliance and accessibility standards
- **Coverage**:
  - Automated accessibility scanning with axe-core
  - Keyboard navigation testing
  - Screen reader compatibility
  - ARIA attributes validation
  - Color contrast and visual accessibility

## Key Features

### Page Object Model (POM)
- **Encapsulation**: UI interactions are encapsulated in page classes
- **Reusability**: Common actions are reusable across tests
- **Maintainability**: UI changes require updates in one location

### API Mocking
- **Predictable Testing**: Consistent API responses for reliable tests
- **Edge Case Coverage**: Mock various scenarios (errors, empty data, slow responses)
- **Isolated Testing**: Frontend tests independent of backend availability

### Comprehensive Fixtures
- **Centralized Data**: All mock data managed in one location
- **Realistic Data**: Mock data mirrors production data structures
- **Easy Maintenance**: Single point of update for test data

### Test Utilities
- **Performance Helpers**: Page load measurement and performance monitoring
- **Visual Testing**: Screenshot utilities with animation controls
- **Network Simulation**: Slow network and offline scenario testing
- **Console Monitoring**: JavaScript error detection and logging

## Configuration

### Playwright Configuration (`playwright.config.ts`)
```typescript
// Multi-browser testing
projects: [
  { name: 'chromium', use: { ...devices['Desktop Chrome'] } },
  { name: 'firefox', use: { ...devices['Desktop Firefox'] } },
  { name: 'webkit', use: { ...devices['Desktop Safari'] } },
  { name: 'mobile', use: { ...devices['iPhone 13'] } }
]

// Accessibility-specific project
{ 
  name: 'accessibility',
  testMatch: '**/*.a11y.spec.ts',
  use: { 
    ...devices['Desktop Chrome'],
    // Additional accessibility testing configurations
  }
}
```

### Test Environment Settings
- **Parallel Execution**: Optimized for CI/CD pipeline performance
- **Visual Regression**: Screenshot comparison with diff highlighting
- **Reporting**: Multiple report formats (HTML, JSON, JUnit)
- **Retry Logic**: Automatic retry for flaky tests

## Running Tests

### Development Commands
```bash
# Run all tests
npx playwright test

# Run specific test suite
npx playwright test dashboard
npx playwright test --grep "accessibility"

# Run with UI mode for debugging
npx playwright test --ui

# Run in headed mode to see browser
npx playwright test --headed

# Run specific browser
npx playwright test --project=firefox
```

### CI/CD Commands
```bash
# Install dependencies and browsers
npx playwright install --with-deps

# Run tests with full reporting
npx playwright test --reporter=html,json,junit

# Run only changed tests
npx playwright test --only-changed
```

## Best Practices

### Test Structure
1. **Arrange**: Set up test data and mock APIs
2. **Act**: Perform user actions through page objects
3. **Assert**: Verify expected outcomes and states

### Data Management
- Use fixtures for consistent test data
- Mock external dependencies
- Clean up test data after each test

### Assertion Patterns
```typescript
// Preferred: Specific assertions
await expect(page.getByRole('button', { name: 'Submit' })).toBeVisible();

// Avoid: Generic text assertions
await expect(page).toHaveText('Submit');
```

### Error Handling
- Test both success and failure scenarios
- Verify error messages and states
- Test network failure conditions

### Performance Considerations
- Use `waitForLoadState('networkidle')` for dynamic content
- Implement custom waits for animations
- Monitor and assert performance metrics

## Debugging

### Common Issues
1. **Timing Issues**: Use proper wait strategies
2. **Flaky Tests**: Implement retry logic and stable selectors
3. **Element Not Found**: Verify selectors and page state

### Debugging Tools
- Playwright Inspector: `npx playwright test --debug`
- Trace Viewer: Generate traces for failed tests
- Console Logs: Monitor browser console during tests

## Maintenance

### Regular Tasks
- Update mock data to match API changes
- Review and update selectors for UI changes
- Monitor test execution times and optimize slow tests
- Update accessibility standards and checks

### Adding New Tests
1. Create appropriate test file in relevant directory
2. Use existing page objects or create new ones
3. Add mock data to fixtures if needed
4. Follow existing naming and structure conventions

## Dependencies

### Required Packages
```json
{
  "@playwright/test": "^1.40.0",
  "@axe-core/playwright": "^4.8.0"
}
```

### Development Dependencies
- TypeScript for type safety
- ESLint for code quality
- Prettier for code formatting

## Integration with CI/CD

### GitHub Actions Example
```yaml
- name: Run Playwright Tests
  run: |
    npx playwright install --with-deps
    npx playwright test
    
- name: Upload Playwright Report
  uses: actions/upload-artifact@v3
  if: always()
  with:
    name: playwright-report
    path: playwright-report/
```

This testing framework provides comprehensive coverage and follows industry best practices to ensure reliable, maintainable, and scalable test automation for the Rocq Agent Toolkit frontend.