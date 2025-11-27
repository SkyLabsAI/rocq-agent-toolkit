import { test, expect, Page } from '@playwright/test';
import AxeBuilder from '@axe-core/playwright';

/**
 * Wait for the page to be fully loaded
 */
async function waitForPageLoad(page: Page) {
    await page.waitForLoadState('domcontentloaded');
    await page.waitForLoadState('networkidle');
}

/**
 * Run accessibility checks on the page
 */
async function checkAccessibility(page: Page) {
    const accessibilityScanResults = await new AxeBuilder({ page }).analyze();
    expect(accessibilityScanResults.violations).toEqual([]);
    return accessibilityScanResults;
}

test.describe('Comparison Features', () => {
    test.describe('Agents Comparison Page', () => {
        test.beforeEach(async ({ page }) => {
            await page.goto('/compare/agents');
            await waitForPageLoad(page);
        });

        test('should load agents comparison page', async ({ page }) => {
            await expect(page).toHaveURL('/compare/agents');

            // Check for comparison table or main content
            const main = page.locator('main, [role="main"], table, [class*="compare"], [class*="table"]');
            await expect(main.first()).toBeVisible();
        });

        test('should pass accessibility checks', async ({ page }) => {
            await checkAccessibility(page);
        });
    });

    test.describe('Runs Comparison Page', () => {
        test.beforeEach(async ({ page }) => {
            await page.goto('/compare');
            await waitForPageLoad(page);
        });

        test('should load runs comparison page', async ({ page }) => {
            await expect(page).toHaveURL('/compare');

            // Check for main content
            const main = page.locator('main, [role="main"]');
            await expect(main.first()).toBeVisible();
        });

        test('should pass accessibility checks', async ({ page }) => {
            await checkAccessibility(page);
        });
    });
});
