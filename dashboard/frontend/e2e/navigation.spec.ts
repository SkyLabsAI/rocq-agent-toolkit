import { test, expect, Page } from '@playwright/test';

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

    test('should navigate to compare agents page', async ({ page }) => {
        await page.goto('/compare/agents');
        await waitForPageLoad(page);

        await expect(page).toHaveURL('/compare/agents');
    });

    test('should navigate to compare runs page', async ({ page }) => {
        await page.goto('/compare');
        await waitForPageLoad(page);

        await expect(page).toHaveURL('/compare');
    });

    test('should show 404 for invalid routes', async ({ page }) => {
        await page.goto('/invalid-route-that-does-not-exist');
        await waitForPageLoad(page);

        // Check for 404 message
        const notFoundText = page.getByText(/404|not found/i);
        await expect(notFoundText).toBeVisible();
    });

    test('should handle deep linking correctly', async ({ page }) => {
        // Test that navigating directly to a deep route works
        await page.goto('/compare/agents');
        await waitForPageLoad(page);

        await expect(page).toHaveURL('/compare/agents');

        // Navigate to another route
        await page.goto('/compare');
        await waitForPageLoad(page);

        await expect(page).toHaveURL('/compare');
    });

    test('should maintain route after page reload', async ({ page }) => {
        // Navigate to a specific route
        await page.goto('/compare/agents');
        await waitForPageLoad(page);

        // Reload the page
        await page.reload();
        await waitForPageLoad(page);

        // Should still be on the same route
        await expect(page).toHaveURL('/compare/agents');
    });

    test('should navigate between routes using browser', async ({ page }) => {
        // Start at homepage
        await page.goto('/');
        await waitForPageLoad(page);

        // Navigate to compare page
        await page.goto('/compare');
        await waitForPageLoad(page);
        await expect(page).toHaveURL('/compare');

        // Navigate to agents compare
        await page.goto('/compare/agents');
        await waitForPageLoad(page);
        await expect(page).toHaveURL('/compare/agents');

        // Use browser back button
        await page.goBack();
        await waitForPageLoad(page);
        await expect(page).toHaveURL('/compare');

        // Use browser forward button
        await page.goForward();
        await waitForPageLoad(page);
        await expect(page).toHaveURL('/compare/agents');

        // Go back to homepage
        await page.goBack();
        await page.goBack();
        await waitForPageLoad(page);
        await expect(page).toHaveURL('/');
    });

    test('should handle multiple rapid route changes', async ({ page }) => {
        await page.goto('/');
        await waitForPageLoad(page);

        // Rapidly change routes
        await page.goto('/compare');
        await page.goto('/compare/agents');
        await page.goto('/');
        await waitForPageLoad(page);

        // Should end up at the last route
        await expect(page).toHaveURL('/');
    });
});
