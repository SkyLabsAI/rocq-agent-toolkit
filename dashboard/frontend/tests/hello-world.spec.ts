
import { test, expect } from './fixtures';

test('homepage loads and shows dashboard', async ({ page }) => {
    await page.goto('/');
    // Check for dashboard title
    await expect(page.getByRole('heading', { name: /Agent Performance/i })).toBeVisible();
    // Check for table
    await expect(page.getByRole('table')).toBeVisible();
});

test('refresh button is visible and clickable', async ({ page }) => {
    await page.goto('/');
    const refreshBtn = page.getByRole('button', { name: /refresh data/i });
    await expect(refreshBtn).toBeVisible();
    await expect(refreshBtn).toBeEnabled();
});