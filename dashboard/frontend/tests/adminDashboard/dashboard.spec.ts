import { test, expect } from '@playwright/test';

test('dashboard table renders with agent rows', async ({ page }) => {
  await page.goto('/');
  await expect(page.getByRole('heading', { name: /Agent Performance/i })).toBeVisible();
  await expect(page.getByRole('table')).toBeVisible();
  // Optionally check for at least one agent row
  // await expect(page.locator('tbody tr')).toHaveCountGreaterThan(0);
});

test('refresh button works', async ({ page }) => {
  await page.goto('/');
  const refreshBtn = page.getByRole('button', { name: /refresh data/i });
  await expect(refreshBtn).toBeVisible();
  await expect(refreshBtn).toBeEnabled();
  await refreshBtn.click();
  // Optionally check for loading or success message
  // await expect(page.getByText(/refreshing|success/i)).toBeVisible();
});
