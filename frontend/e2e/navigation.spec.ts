import { expect, type Page, test } from '@playwright/test';

/**
 * Wait for the page to be fully loaded
 */
async function waitForPageLoad(page: Page) {
  await page.waitForLoadState('domcontentloaded');
  await page.waitForLoadState('networkidle');
}

test.describe('Navigation and Routing', () => {
  test('should navigate to homepage', async ({ page }) => {
    await page.goto('/');
    await waitForPageLoad(page);

    await expect(page).toHaveURL('/');
  });
});
