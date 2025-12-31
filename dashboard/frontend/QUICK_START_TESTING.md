# Quick Start - Testing the Visualizer

This is a quick reference guide to get you started testing the visualizer with Playwright codegen.

## Prerequisites

```bash
# Install dependencies (if not already done)
pnpm install
```

## Step 1: Enable Mock Data

Create or update `.env.local`:

```bash
USE_MOCK_DATA=true
```

## Step 2: Start Development Server

```bash
pnpm dev
```

The app should start at `http://localhost:3000`

## Step 3: Run Existing Tests

```bash
# Run all Playwright tests
pnpm playwright test

# Run only visualizer tests
pnpm playwright test visualizer

# Run with UI (recommended for first time)
pnpm playwright test --ui
```

## Step 4: Generate New Tests with Codegen

```bash
# Start Playwright codegen
pnpm playwright codegen http://localhost:3000
```

This opens two windows:
1. **Browser window** - Interact with your app
2. **Playwright Inspector** - See generated code

## Step 5: Record Your Test

In the browser window, perform these actions:

### Basic Visualizer Flow:
1. **Click** on an agent row (e.g., "agentA")
2. **Wait** for instances to load (1 second)
3. **Click** on an instance row
4. **Wait** for runs to load (1 second)
5. **Click** on a run row's visualizer button
6. **Wait** for modal to open (2 seconds)
7. **Click** on a span node in the graph
8. **Wait** for logs to load (1.5 seconds)
9. **Click** depth button "2"
10. **Click** "Show Raw JSON" button
11. **Click** close button

### What to Look For:

**Agent Row**: `[data-testid^="agent-row-"]`
**Instance Row**: `[data-testid^="instance-row-"]`
**Run Row**: `[data-testid^="run-row-"]`
**Visualizer Modal**: `[role="dialog"]`
**Span Nodes**: `[data-span-id]` or `[class*="span-node"]`
**Depth Buttons**: `button` with text "1", "2", "3", "4", "5", or "All"
**Logs Section**: Text containing "Logs"

## Step 6: Copy Generated Code

From the Playwright Inspector, copy the generated code and paste it into a test file:

```typescript
// e2e/my-visualizer-test.spec.ts
import { expect, test } from '@playwright/test';
import { takeScreenshot, waitForPageLoad } from './utils/test-helpers';

test.describe('My Visualizer Test', () => {
  test('should do something', async ({ page }) => {
    // Paste generated code here
    await page.goto('http://localhost:3000/');
    // ... rest of generated code
  });
});
```

## Step 7: Enhance Generated Code

Add assertions and screenshots:

```typescript
test('should open visualizer and select span', async ({ page }) => {
  await page.goto('http://localhost:3000/');
  await waitForPageLoad(page);

  // Click agent
  await page.getByTestId('agent-row-agentA').click();
  await page.waitForTimeout(1000);
  await takeScreenshot(page, 'my-test', '01-agent-expanded');

  // Click instance
  await page.getByTestId('instance-row-0').click();
  await page.waitForTimeout(1000);

  // Click visualizer button
  const runRow = page.getByTestId('run-row-0');
  await runRow.locator('button').first().click();
  await page.waitForTimeout(2000);

  // Assert modal is open
  await expect(page.getByRole('dialog')).toBeVisible();
  await takeScreenshot(page, 'my-test', '02-visualizer-opened');

  // Click span
  await page.locator('[data-span-id]').first().click();
  await page.waitForTimeout(1500);

  // Assert span details visible
  await expect(page.getByText('Span details')).toBeVisible();
  await takeScreenshot(page, 'my-test', '03-span-selected');
});
```

## Step 8: Run Your New Test

```bash
pnpm playwright test my-visualizer-test
```

## Common Patterns

### Wait for Element
```typescript
await page.waitForSelector('[data-testid="my-element"]');
```

### Click with Retry
```typescript
await page.getByTestId('my-button').click({ timeout: 5000 });
```

### Assert Visibility
```typescript
await expect(page.getByText('My Text')).toBeVisible();
```

### Take Screenshot
```typescript
await takeScreenshot(page, 'folder-name', 'screenshot-name');
```

### Handle Optional Elements
```typescript
const element = page.getByTestId('optional-element');
if ((await element.count()) > 0) {
  await element.click();
}
```

## Debugging

### Run in Headed Mode
```bash
pnpm playwright test --headed
```

### Run with Debug
```bash
pnpm playwright test --debug
```

### View Test Report
```bash
pnpm playwright show-report
```

## Tips

1. **Use data-testid** - Most reliable selector
2. **Add waits** - Give time for animations and API calls
3. **Add assertions** - Verify expected outcomes
4. **Take screenshots** - Visual verification
5. **Group tests** - Use `test.describe()` blocks
6. **Handle errors gracefully** - Check element count before clicking

## Mock Data Features

The visualizer mock data includes:

- ✅ **5-15 traces per run** - Realistic variety
- ✅ **Hierarchical span tree** - Root → children → nested
- ✅ **Realistic timing** - Proper nanosecond timestamps
- ✅ **Rich attributes** - Model names, token counts, etc.
- ✅ **5-20 logs per span** - Structured log entries
- ✅ **Multiple log levels** - DEBUG, INFO, WARN, ERROR
- ✅ **Simulated delays** - 200-1500ms network latency

## Example: Complete Test

```typescript
import { expect, test } from '@playwright/test';
import { takeScreenshot, waitForPageLoad } from './utils/test-helpers';

test.describe('Visualizer - Quick Test', () => {
  test('complete visualizer flow', async ({ page }) => {
    // 1. Navigate
    await page.goto('http://localhost:3000/');
    await waitForPageLoad(page);

    // 2. Expand agent
    await page.getByTestId('agent-row-agentA').click();
    await page.waitForTimeout(1000);

    // 3. Expand instance
    const instance = page.getByTestId('instance-row-0');
    if ((await instance.count()) > 0) {
      await instance.click();
      await page.waitForTimeout(1000);
    }

    // 4. Open visualizer
    const run = page.getByTestId('run-row-0');
    await run.locator('button').first().click();
    await page.waitForTimeout(2000);
    await expect(page.getByRole('dialog')).toBeVisible();

    // 5. Select span
    const span = page.locator('[data-span-id]').first();
    if ((await span.count()) > 0) {
      await span.click();
      await page.waitForTimeout(1500);
      await expect(page.getByText('Span details')).toBeVisible();
    }

    // 6. Change depth
    const depth2 = page.getByRole('button', { name: '2' });
    if ((await depth2.count()) > 0) {
      await depth2.click();
      await page.waitForTimeout(500);
    }

    // 7. Screenshot
    await takeScreenshot(page, 'quick-test', 'complete');

    // 8. Close
    const close = page.getByRole('button', { name: /close/i });
    if ((await close.count()) > 0) {
      await close.click();
    }
  });
});
```

## Next Steps

1. ✅ Run the example tests
2. ✅ Use codegen to record your own tests
3. ✅ Add assertions and screenshots
4. ✅ Organize tests into describe blocks
5. ✅ Run tests regularly during development

## Resources

- **Full Guide**: See `e2e/PLAYWRIGHT_CODEGEN_GUIDE.md`
- **Mock Data Docs**: See `services/mockdata/README.md`
- **Summary**: See `MOCKDATA_REFACTOR_SUMMARY.md`
- **Playwright Docs**: https://playwright.dev/docs/intro

---

**Quick Reference Complete!** 🚀

Start with: `pnpm playwright codegen http://localhost:3000`

