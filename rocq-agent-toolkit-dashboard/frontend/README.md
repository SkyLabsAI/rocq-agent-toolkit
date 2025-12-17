## RAT Public Dashboard

This directory contains the public dashboard UI built with **Next.js (App Router)** and **TypeScript**. It was copied into this mono-repo and is now managed by the main repository (not as a submodule).

### 1. Prerequisites

Install / have:

1. Node.js (recommend 18.x LTS or newer) – check:
```bash
node -v
```
2. Install pnpm globally (preferred package manager):
```bash
npm install -g pnpm
```

Optional checks:
```bash
pnpm -v
```

### 2. Install Dependencies

From the repository root or inside this folder:
```bash
cd rat-public-dashboard
pnpm install
```
This will read `pnpm-lock.yaml` and install exact versions.

### 3. Run the Development Server

```bash
pnpm run dev
```

Then open:
```
http://localhost:3000
```

Hot reload is enabled. Edit `app/page.tsx` or any component under `app/` or `components/` and the browser will refresh automatically.

### 4. Common Scripts

```bash
pnpm run dev      # start local dev server
pnpm run build    # production build
pnpm start        # run built app
pnpm lint         # run ESLint
```

### 5. End-to-End Testing with Playwright

This project uses Playwright for end-to-end testing.

#### 5.1 Install Playwright Browsers (First Time Only)

Before running E2E tests for the first time, install Playwright browsers:
```bash
pnpm run test:e2e:install
```

#### 5.2 Running E2E Tests

```bash
# Run all tests (headless mode)
pnpm run test:e2e

# Run tests in UI mode (interactive, great for development)
pnpm run test:e2e:ui

# Run tests in headed mode (watch the browser)
pnpm run test:e2e:headed

# Debug tests step by step
pnpm run test:e2e:debug

# View last test report
pnpm run test:e2e:report
```

#### 5.3 Running Specific Tests

```bash
# Run a specific test file
pnpm exec playwright test e2e/home.spec.ts

# Run tests matching a pattern
pnpm exec playwright test --grep "navigation"

# Run tests in a specific project (browser)
pnpm exec playwright test --project=chromium
```

#### 5.4 Writing New Tests

Tests are located in the `e2e/` directory:
- `e2e/home.spec.ts` - Homepage/dashboard tests
- `e2e/navigation.spec.ts` - Routing and navigation tests
- `e2e/task-details.spec.ts` - Task details modal tests
- `e2e/compare.spec.ts` - Comparison features tests

Example test structure:
```typescript
import { test, expect } from '../fixtures/baseFixtures';
import { waitForPageLoad } from '../utils/testHelpers';

test.describe('My Feature', () => {
  test('should do something', async ({ page }) => {
    await page.goto('/my-route');
    await waitForPageLoad(page);
    
    // Your test assertions
    await expect(page.locator('.my-element')).toBeVisible();
  });
});
```

#### 5.5 Test Utilities

Use helpers from `e2e/utils/testHelpers.ts`:
- `waitForPageLoad(page)` - Wait for page to fully load
- `waitForElement(page, selector)` - Wait for element to be visible
- `checkAccessibility(page)` - Run accessibility checks with axe-core
- `isElementVisible(page, selector)` - Check element visibility

#### 5.6 CI/CD Integration

Tests automatically start the Next.js dev server before running. In CI environments:
- Tests run with 1 retry on failure
- Tests run in parallel where possible
- HTML reports are generated in `playwright-report/`
- Screenshots and videos are captured on failure

### 6. Environment Variables (If Needed)

If this project later requires runtime configuration, create a `.env.local` file in this folder. Example:
```env
NEXT_PUBLIC_API_BASE_URL=http://localhost:8000
```
Never commit secrets; `.env.local` should be gitignored.

### 7. Updating Dependencies

```bash
pnpm add <package>
pnpm remove <package>
```

### 8. Troubleshooting

- If you see module resolution errors: delete `node_modules` and run `pnpm install` again.
- If pnpm complains about store corruption: `pnpm store prune`.
- If port 3000 is busy: `pnpm run dev -- --port=3001`.

### 9. Learn More (Optional Links)

- Next.js Docs: https://nextjs.org/docs
- App Router Basics: https://nextjs.org/docs/app/building-your-application/routing
- pnpm Docs: https://pnpm.io

### 10. Production Build & Run


```bash
pnpm run build
pnpm start
```
This serves the built output (defaults to port 3000 unless changed).

---
Maintained as part of the main repository. Update this README if setup steps change.
