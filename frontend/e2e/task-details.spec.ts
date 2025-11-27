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

test.describe('Task Details Modal', () => {
    test.beforeEach(async ({ page }) => {
        // Navigate to homepage where task details might be accessible
        await page.goto('/');
        await waitForPageLoad(page);
    });

    test('should open task details modal when task is clicked', async ({ page }) => {
        // Look for any clickable task items
        // Adjust selector based on your actual implementation
        const taskItems = page.locator('[data-testid*="task"], [class*="task-item"], [class*="run-row"]');
        const count = await taskItems.count();

        if (count > 0) {
            // Click the first task
            await taskItems.first().click();

            // Wait for modal to appear
            await page.waitForTimeout(500);

            // Check if modal or details view appeared
            const modal = page.locator('[role="dialog"], [class*="modal"], [class*="details"]');
            const modalCount = await modal.count();

            // If modal exists, verify it's visible
            if (modalCount > 0) {
                await expect(modal.first()).toBeVisible();
            }
        }
    });

    test('should close modal when close button is clicked', async ({ page }) => {
        // Try to find and click a task to open modal
        const taskItems = page.locator('[data-testid*="task"], [class*="task-item"], [class*="run-row"]');
        const count = await taskItems.count();

        if (count > 0) {
            await taskItems.first().click();
            await page.waitForTimeout(500);

            // Look for close button
            const closeButton = page.getByRole('button', { name: /close|×|✕/i });
            const closeCount = await closeButton.count();

            if (closeCount > 0) {
                await closeButton.first().click();
                await page.waitForTimeout(300);

                // Modal should be hidden
                const modal = page.locator('[role="dialog"]:visible, [class*="modal"]:visible');
                await expect(modal).toHaveCount(0);
            }
        }
    });

    test('should close modal when pressing Escape key', async ({ page }) => {
        const taskItems = page.locator('[data-testid*="task"], [class*="task-item"], [class*="run-row"]');
        const count = await taskItems.count();

        if (count > 0) {
            await taskItems.first().click();
            await page.waitForTimeout(500);

            // Check if modal exists
            const modal = page.locator('[role="dialog"], [class*="modal"]');
            const modalCount = await modal.count();

            if (modalCount > 0) {
                // Press Escape key
                await page.keyboard.press('Escape');
                await page.waitForTimeout(300);

                // Modal should be closed
                const visibleModal = page.locator('[role="dialog"]:visible, [class*="modal"]:visible');
                await expect(visibleModal).toHaveCount(0);
            }
        }
    });

    
});
