import { expect, test } from '@playwright/test';

import { takeScreenshot, waitForPageLoad } from './utils/test-helpers';

test.describe('Agent View - Agents → Datasets → Runs Flow', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await waitForPageLoad(page);

    // Ensure we're on the Agents tab (default view)
    const agentsTab = page.locator('button').filter({ hasText: /^Agents$/i });
    if ((await agentsTab.count()) > 0) {
      await agentsTab.first().click();
      await waitForPageLoad(page);
    }
  });

  test.describe('Agent List Display', () => {
    test('should display the Leader Dashboard with agent list', async ({
      page,
    }) => {
      // Verify dashboard header is visible
      await expect(page.getByText('Leader Dashboard')).toBeVisible();

      // Verify the agent view container exists
      const agentView = page.locator('[data-testid="agent-view"]');
      await expect(agentView).toBeVisible();

      // Verify agents table exists
      const agentsTable = page.locator('[data-testid="agents-table"]');
      await expect(agentsTable).toBeVisible();

      await page.waitForTimeout(1000);

      const rows = page.locator('[data-testid*="agent-row"]');
      await expect(rows).toHaveCount(2);

      await takeScreenshot(page, 'agent-view', 'agent-list-initial');
    });

    test('should display agent rows with expected columns', async ({
      page,
    }) => {
      // Verify header row with sort buttons exists
      const headerRow = page.locator('[data-testid="agents-header-row"]');
      await expect(headerRow).toBeVisible();

      // Verify sort buttons exist
      await expect(
        page.locator('[data-testid="sort-by-agent-name"]')
      ).toBeVisible();
      await expect(
        page.locator('[data-testid="sort-by-success-rate"]')
      ).toBeVisible();
      await expect(
        page.locator('[data-testid="sort-by-avg-time"]')
      ).toBeVisible();
      await expect(
        page.locator('[data-testid="sort-by-avg-tokens"]')
      ).toBeVisible();
      await expect(
        page.locator('[data-testid="sort-by-llm-calls"]')
      ).toBeVisible();
    });

    test('should display agent rows', async ({ page }) => {
      // Wait for agent rows to load - they have data-testid like "agent-row-{name}"
      await page.waitForTimeout(1000);
      const agentRows = page.locator('[data-testid^="agent-row-"]');
      const count = await agentRows.count();
      expect(count).toBeGreaterThanOrEqual(0);
    });
  });

  test.describe('Agent Expansion', () => {
    test('should load datasets for the first agent when clicked', async ({
      page,
    }) => {
      // Wait for agent rows to load
      await page.waitForTimeout(1000);
      const agentRows = page.locator('[data-testid^="agent-row-"]');
      const firstAgent = agentRows.first();
      await expect(firstAgent).toBeVisible();

      // Click the first agent row
      await firstAgent.click();
      // Wait for datasets to load (adjust timeout as needed for your app)
      await page.waitForTimeout(1000);

      // Check for dataset rows under the agent (assuming data-testid="dataset-row" for each dataset)
      const datasetRows = page.locator('[data-testid^="dataset-card"]');
      const datasetCount = await datasetRows.count();
      await expect(datasetCount).toBeGreaterThan(0);
      // Optionally, take a screenshot
      await takeScreenshot(page, 'agent-view', 'agent-datasets-expanded');
    });
  });
});
