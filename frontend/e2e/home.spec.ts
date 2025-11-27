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

test.describe('Homepage / Dashboard', () => {
    test.beforeEach(async ({ page }) => {
        // Navigate to homepage before each test
        await page.goto('/');
    });

    test('should load the homepage successfully', async ({ page }) => {
        // Check that the page loaded
        await expect(page).toHaveURL('/');

        // Wait for page to be fully loaded
        await waitForPageLoad(page);

        // Verify page title or heading exists
        await expect(page).toHaveTitle(/RAT Public Dashboard|Dashboard/i);
    });

    test('should display main dashboard components', async ({ page }) => {
        await waitForPageLoad(page);

        // Check for LocalDashboard component rendering
        // This will depend on your actual dashboard structure
        const main = page.locator('main, [role="main"], .dashboard');
        await expect(main).toBeVisible();
    });

    test('should have theme switcher', async ({ page }) => {
        await waitForPageLoad(page);

        // Look for theme switcher button/component
        // Adjust selector based on your ThemeSwitcher implementation
        const themeSwitcher = page.getByRole('button', { name: /theme|dark|light/i });

        // If theme switcher exists, it should be visible
        const count = await themeSwitcher.count();
        if (count > 0) {
            await expect(themeSwitcher.first()).toBeVisible();
        }
    });

    test('should toggle theme when theme switcher is clicked', async ({ page }) => {
        await waitForPageLoad(page);

        // Look for theme switcher
        const themeSwitcher = page.getByRole('button', { name: /theme|dark|light/i });
        const count = await themeSwitcher.count();

        if (count > 0) {
            // Get initial theme (check html or body class)
            const initialTheme = await page.evaluate(() => {
                return document.documentElement.classList.contains('dark') ||
                    document.body.classList.contains('dark');
            });

            // Click theme switcher
            await themeSwitcher.first().click();

            // Wait a bit for theme to change
            await page.waitForTimeout(300);

            // Check theme has changed
            const newTheme = await page.evaluate(() => {
                return document.documentElement.classList.contains('dark') ||
                    document.body.classList.contains('dark');
            });

            expect(newTheme).not.toBe(initialTheme);
        }
    });

    test('should pass basic accessibility checks', async ({ page }) => {
        await waitForPageLoad(page);

        // Run accessibility scan
        await checkAccessibility(page);
    });

    test('should have no console errors on load', async ({ page }) => {
        const consoleErrors: string[] = [];

        // Listen for console errors
        page.on('console', (msg) => {
            if (msg.type() === 'error') {
                consoleErrors.push(msg.text());
            }
        });

        await page.goto('/');
        await waitForPageLoad(page);

        // Check for no critical console errors
        // Filter out known harmless errors if any
        const criticalErrors = consoleErrors.filter(
            (error) => !error.includes('favicon') // Example: ignore favicon errors
        );

        expect(criticalErrors).toHaveLength(0);
    });
});
