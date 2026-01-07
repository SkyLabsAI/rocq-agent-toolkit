# Playwright Codegen Guide

This guide explains how to use Playwright's codegen feature to generate tests for the visualizer and other features.

## Prerequisites

Make sure you have Playwright installed:

```bash
pnpm install
```

## Starting the Application

Before using codegen, start your development server:

```bash
# Terminal 1: Start the frontend
pnpm dev
```

The app should be running at `http://localhost:3000` (or the port specified in your config).

## Using Playwright Codegen

### Basic Usage

Open Playwright's test generator:

```bash
pnpm playwright codegen http://localhost:3000
```

This will:
1. Open a browser window
2. Open the Playwright Inspector
3. Start recording your interactions

### Recording a Test

1. **Navigate and Interact**: Click through your application as a user would
2. **Inspect Elements**: Use the "Explore" button to find good selectors
3. **Copy Code**: The generated code appears in the Playwright Inspector
4. **Paste into Test File**: Copy the code into your `.spec.ts` file

### Example: Recording a Visualizer Test

```bash
# Start codegen
pnpm playwright codegen http://localhost:3000

# Then perform these actions in the browser:
# 1. Click on an agent row
# 2. Click on an instance row
# 3. Click on a run row
# 4. Click the visualizer button
# 5. Select a trace from the dropdown
# 6. Click on a span node
# 7. Change the depth level
# 8. View the logs
# 9. Close the modal
```

The generated code will look something like:

```typescript
test('visualizer flow', async ({ page }) => {
  await page.goto('http://localhost:3000/');
  await page.getByTestId('agent-row-agentA').click();
  await page.getByTestId('instance-row-0').click();
  await page.getByTestId('run-row-0').locator('button').first().click();
  // ... more actions
});
```

## Advanced Codegen Options

### Specify Device Emulation

```bash
# Test on mobile
pnpm playwright codegen --device="iPhone 13" http://localhost:3000

# Test on tablet
pnpm playwright codegen --device="iPad Pro" http://localhost:3000
```

### Save Output Directly to File

```bash
pnpm playwright codegen --target typescript --output e2e/my-new-test.spec.ts http://localhost:3000
```

### Use Custom Browser

```bash
# Use Firefox
pnpm playwright codegen --browser=firefox http://localhost:3000

# Use WebKit (Safari)
pnpm playwright codegen --browser=webkit http://localhost:3000
```

### Set Viewport Size

```bash
pnpm playwright codegen --viewport-size=1280,720 http://localhost:3000
```

## Testing with Mock Data

To ensure consistent test results, use mock data:

### Enable Mock Data

Set the environment variable before starting codegen:

```bash
# In your .env.local file
USE_MOCK_DATA=true

# Or export it in your terminal
export USE_MOCK_DATA=true
pnpm dev
```

Then run codegen:

```bash
pnpm playwright codegen http://localhost:3000
```

## Best Practices

### 1. Use Data Test IDs

When recording, look for elements with `data-testid` attributes:

```typescript
// Good - uses data-testid
await page.getByTestId('agent-row-agentA').click();

// Less reliable - uses text content
await page.getByText('agentA').click();

// Avoid - uses CSS classes
await page.locator('.agent-row').first().click();
```

### 2. Add Waits for Dynamic Content

After recording, add appropriate waits:

```typescript
await page.getByTestId('agent-row-agentA').click();
await page.waitForTimeout(1000); // Wait for expansion animation
// Or better:
await page.waitForSelector('[data-testid^="instance-row-"]');
```

### 3. Add Assertions

Codegen doesn't generate assertions automatically. Add them:

```typescript
await page.getByTestId('visualizer-modal').click();
// Add assertion:
await expect(page.getByRole('dialog')).toBeVisible();
```

### 4. Group Related Actions

Organize your generated code into logical test blocks:

```typescript
test.describe('Visualizer Flow', () => {
  test('should open visualizer', async ({ page }) => {
    // Navigation code here
  });

  test('should display spans', async ({ page }) => {
    // Span interaction code here
  });
});
```

### 5. Take Screenshots

Add screenshots for visual verification:

```typescript
await page.getByTestId('visualizer-modal').click();
await takeScreenshot(page, 'visualizer', 'modal-opened');
```

## Debugging Generated Tests

### Run in Headed Mode

```bash
pnpm playwright test --headed
```

### Run with Debug Mode

```bash
pnpm playwright test --debug
```

### Run Specific Test

```bash
pnpm playwright test visualizer.spec.ts
```

### Run with UI Mode

```bash
pnpm playwright test --ui
```

## Common Issues and Solutions

### Issue: Elements Not Found

**Problem**: `Error: Locator not found`

**Solution**: Add waits or use more specific selectors:

```typescript
// Before
await page.locator('button').click();

// After
await page.waitForSelector('[data-testid="my-button"]');
await page.getByTestId('my-button').click();
```

### Issue: Flaky Tests

**Problem**: Tests pass sometimes, fail other times

**Solution**: Add proper waits and assertions:

```typescript
// Wait for network requests to complete
await page.waitForLoadState('networkidle');

// Wait for specific elements
await expect(page.getByTestId('data-loaded')).toBeVisible();
```

### Issue: Modal Not Appearing

**Problem**: Modal doesn't open when expected

**Solution**: Ensure proper click and wait:

```typescript
await page.getByTestId('open-modal-button').click();
await page.waitForSelector('[role="dialog"]', { state: 'visible' });
await expect(page.getByRole('dialog')).toBeVisible();
```

## Visualizer-Specific Tips

### Testing Trace Selection

```typescript
// Wait for traces to load
await page.waitForTimeout(2000);

// Select a trace
const traceSelect = page.locator('select').first();
await traceSelect.selectOption({ index: 1 });

// Verify spans loaded
await expect(page.locator('[data-span-id]').first()).toBeVisible();
```

### Testing Span Interaction

```typescript
// Click a span node
const spanNode = page.locator('[data-span-id]').first();
await spanNode.click();

// Verify details panel updated
await expect(page.getByText('Span details')).toBeVisible();
await expect(page.getByText('Attributes')).toBeVisible();
```

### Testing Depth Control

```typescript
// Click depth button
await page.getByRole('button', { name: '2' }).click();

// Verify button is selected
const depthButton = page.getByRole('button', { name: '2' });
await expect(depthButton).toHaveClass(/bg-primary/);
```

### Testing Logs Display

```typescript
// Select a span to trigger logs
await page.locator('[data-span-id]').first().click();

// Wait for logs to load
await page.waitForTimeout(1500);

// Verify logs section
await expect(page.getByText('Logs')).toBeVisible();

// Toggle to raw view
await page.getByRole('button', { name: /show raw json/i }).click();
await expect(page.locator('pre').filter({ hasText: /{/ })).toBeVisible();
```

## Running the Complete Test Suite

### Run All Tests

```bash
pnpm playwright test
```

### Run Visualizer Tests Only

```bash
pnpm playwright test visualizer
```

### Run Tests in Parallel

```bash
pnpm playwright test --workers=4
```

### Generate HTML Report

```bash
pnpm playwright test --reporter=html
```

### View Last Test Report

```bash
pnpm playwright show-report
```

## Next Steps

1. **Record Your Tests**: Use codegen to record interactions
2. **Refine Selectors**: Replace generated selectors with data-testid attributes
3. **Add Assertions**: Verify expected outcomes
4. **Add Screenshots**: Document visual states
5. **Organize Tests**: Group related tests into describe blocks
6. **Run Regularly**: Integrate into CI/CD pipeline

## Additional Resources

- [Playwright Documentation](https://playwright.dev/docs/intro)
- [Playwright Codegen Guide](https://playwright.dev/docs/codegen)
- [Playwright Best Practices](https://playwright.dev/docs/best-practices)
- [Playwright Selectors](https://playwright.dev/docs/selectors)

## Example: Complete Visualizer Test Flow

Here's a complete example of a well-structured visualizer test:

```typescript
import { expect, test } from '@playwright/test';
import { takeScreenshot, waitForPageLoad } from './utils/test-helpers';

test.describe('Visualizer - Complete Flow', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await waitForPageLoad(page);
  });

  test('should complete full visualizer workflow', async ({ page }) => {
    // Step 1: Navigate to agent
    await page.getByTestId('agent-row-agentA').click();
    await page.waitForTimeout(1000);
    await takeScreenshot(page, 'visualizer', '01-agent-expanded');

    // Step 2: Open instance
    await page.getByTestId('instance-row-0').click();
    await page.waitForTimeout(1000);
    await takeScreenshot(page, 'visualizer', '02-instance-expanded');

    // Step 3: Open visualizer
    const runRow = page.getByTestId('run-row-0');
    await runRow.locator('button').first().click();
    await page.waitForTimeout(2000);
    await expect(page.getByRole('dialog')).toBeVisible();
    await takeScreenshot(page, 'visualizer', '03-visualizer-opened');

    // Step 4: Select a span
    await page.locator('[data-span-id]').first().click();
    await page.waitForTimeout(1500);
    await expect(page.getByText('Span details')).toBeVisible();
    await takeScreenshot(page, 'visualizer', '04-span-selected');

    // Step 5: Change depth
    await page.getByRole('button', { name: '2' }).click();
    await page.waitForTimeout(500);
    await takeScreenshot(page, 'visualizer', '05-depth-changed');

    // Step 6: View logs
    await expect(page.getByText('Logs')).toBeVisible();
    await takeScreenshot(page, 'visualizer', '06-logs-displayed');

    // Step 7: Close modal
    await page.getByRole('button', { name: /close/i }).click();
    await page.waitForTimeout(500);
    await expect(page.getByRole('dialog')).not.toBeVisible();
    await takeScreenshot(page, 'visualizer', '07-modal-closed');
  });
});
```

Happy testing! 🎭

