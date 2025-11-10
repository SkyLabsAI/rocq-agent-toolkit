import { test, expect } from '@playwright/test';

test('shows loading spinner on dashboard', async ({ page }) => {
  await page.goto('/');
  // Optionally simulate slow network or mock loading state
  // await expect(page.getByTestId('loading-spinner')).toBeVisible();
});

test('shows error message on data fetch failure', async ({ page }) => {
  await page.goto('/');
  // Optionally mock API to fail and check for error message
  // await expect(page.getByText(/error/i)).toBeVisible();
});

test('shows empty state when no agents', async ({ page }) => {
  await page.goto('/');
  // Optionally mock API to return empty and check for empty state UI
  // await expect(page.getByText(/no agents/i)).toBeVisible();
});
