# Playwright Testing Guide

## 🚀 Running Tests

### Basic Commands
```bash
# Run all tests
npm run test:e2e
# or
npx playwright test

# Run tests with UI mode (interactive)
npm run test:e2e:ui
# or
npx playwright test --ui

# Run tests in headed mode (see browser)
npm run test:e2e:headed
# or
npx playwright test --headed

# Run specific test file
npx playwright test tests/basic.spec.ts

# Run tests matching a pattern
npx playwright test --grep "dashboard"
```

### Advanced Commands
```bash
# Debug mode (step through tests)
npm run test:e2e:debug
# or
npx playwright test --debug

# Run only failed tests from last run
npx playwright test --last-failed

# Run tests in specific browser
npx playwright test --project=chromium
npx playwright test --project=firefox
npx playwright test --project=webkit

# Run with different reporters
npx playwright test --reporter=dot
npx playwright test --reporter=json
npx playwright test --reporter=junit
```

## 📊 Viewing Test Results

### 1. HTML Report (Recommended)
```bash
# Generate and open HTML report
npm run test:e2e:report
# or
npx playwright show-report

# If port is busy, try with different port
npx playwright show-report --port=9324
```

### 2. Console Output
The console shows real-time results:
- ✓ Passed tests (green)
- ✘ Failed tests (red) 
- Interrupted tests
- Test duration and performance metrics

### 3. Test Results Files
```bash
# View JSON results
cat test-results/results.json

# View JUnit XML (for CI/CD)
cat test-results/junit.xml
```

## 🎯 Test Categories Available

### Dashboard Tests
```bash
npx playwright test tests/dashboard/
```

### Modal Tests  
```bash
npx playwright test tests/taskModal/
```

### Integration Tests
```bash
npx playwright test tests/integration/
```

### Accessibility Tests
```bash
npx playwright test tests/accessibility/
```

## 🔧 Before Running Tests

### Option 1: Start Dev Server Manually
```bash
# Terminal 1: Start the app
npm run dev

# Terminal 2: Run tests  
npx playwright test
```

### Option 2: Auto-start in Config
The `playwright.config.ts` can be configured to auto-start the server:

```typescript
// Add to playwright.config.ts
webServer: {
  command: 'npm run dev',
  url: 'http://localhost:3000',
  reuseExistingServer: !process.env.CI,
}
```

## 📈 Understanding Test Results

### HTML Report Features:
- **Test Overview**: Pass/fail statistics
- **Test Details**: Individual test results with screenshots
- **Error Traces**: Detailed error information and stack traces  
- **Screenshots**: Visual evidence of failures
- **Videos**: Recordings of test runs (on failures)
- **Performance Metrics**: Load times and performance data

### Console Output Meaning:
```
✓ 4 passed (13.0s)    # 4 tests passed in 13 seconds
✘ 2 failed            # 2 tests failed
- 4 interrupted        # 4 tests were stopped/interrupted
```

## 🐛 Debugging Failed Tests

### 1. Run in Debug Mode
```bash
npx playwright test --debug tests/failing-test.spec.ts
```

### 2. Check Screenshots
Failed tests automatically capture screenshots in `test-results/`

### 3. View Traces
```bash
npx playwright show-trace test-results/trace.zip
```

### 4. Check Console Logs
Look for JavaScript errors in the HTML report

## ⚡ Performance Tips

### Run Faster
```bash
# Run in parallel with more workers
npx playwright test --workers=4

# Run only chromium for speed
npx playwright test --project=chromium

# Skip slow tests
npx playwright test --grep-invert="slow"
```

### CI/CD Mode
```bash
# Optimized for CI
CI=true npx playwright test
```

## 🎨 Visual Testing
```bash
# Update visual snapshots
npx playwright test --update-snapshots

# Compare visual changes
npx playwright test --reporter=html
```

## 📱 Mobile Testing
```bash
# Run mobile tests
npx playwright test --project=mobile
```

This setup provides comprehensive test coverage with detailed reporting and debugging capabilities!