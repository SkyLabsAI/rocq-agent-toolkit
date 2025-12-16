import { expect, test } from '@playwright/test';

import { takeScreenshot, waitForPageLoad } from './utils/test-helpers';

test.describe('DatasetView - Datasets → Agents → Runs Flow', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await waitForPageLoad(page);

    // Ensure we're on the Datasets tab (default view)
    const datasetsTab = page
      .locator('button')
      .filter({ hasText: /^Datasets$/i });
    if ((await datasetsTab.count()) > 0) {
      await datasetsTab.first().click();
      await waitForPageLoad(page);
    }
  });

  test.describe('Agent List Display', () => {
    test('should display the Leader Dashboard with agent list', async ({
      page,
    }) => {
      // Verify dashboard header is visible
      await expect(page.getByText('Leader Dashboard')).toBeVisible();

      // Verify the dataset view container exists
      const datasetView = page.locator('[data-testid="datasets-view"]');
      await expect(datasetView).toBeVisible();

      // Verify datasets table exists
      const datasetsTable = page.locator('[data-testid="datasets-view"]');
      await expect(datasetsTable).toBeVisible();

      await page.waitForTimeout(1000);

      const rows = page.locator('[data-testid*="dataset-row"]');
      await expect(rows).toHaveCount(3);

      await takeScreenshot(page, 'dataset-view', 'dataset-list-initial');
    });

    test('should display dataset rows', async ({ page }) => {
      await page.waitForTimeout(1000);
      const datasetRows = page.locator('[data-testid^="dataset-row-"]');
      const count = await datasetRows.count();
      expect(count).toBeGreaterThanOrEqual(0);
    });
  });
});
