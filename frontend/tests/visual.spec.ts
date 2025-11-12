import { test, expect } from './fixtures';
import { setupDefaultMocks } from './utils/apiMocker';

test.describe('Visual Screenshot Tests', () => {
  test.beforeEach(async ({ page }) => {
    await setupDefaultMocks(page);
  });

  test('visual dashboard screenshot', async ({ page }) => {
    await page.goto('/');
    
    // Wait for dashboard to load
    await expect(page.getByRole('heading', { name: /Agent Performance/i })).toBeVisible();
    await page.waitForTimeout(2000); // Let animations settle
    
    // Take screenshot
    await expect(page).toHaveScreenshot('dashboard-overview.png');
  });

  test('visual agent details screenshot', async ({ page }) => {
    await page.goto('/');
    
    // Wait for table to load
    await expect(page.getByRole('table')).toBeVisible();
    await page.waitForTimeout(1000);
    
    // Click on first agent row to expand details
    const firstRow = page.locator('table tbody tr').first();
    await firstRow.click();
    
    // Wait for details to load
    await page.waitForTimeout(1000);
    
    // Take screenshot
    await expect(page).toHaveScreenshot('agent-details-expanded.png');
  });

  test('visual task modal screenshot', async ({ page }) => {
    await page.goto('/');
    
    // Wait for table to load
    await expect(page.getByRole('table')).toBeVisible();
    await page.waitForTimeout(1000);
    
    // Click on first agent to expand
    const firstRow = page.locator('table tbody tr').first();
    await firstRow.click();
    await page.waitForTimeout(500);
    
    // Click on a task details button if available
    const taskButton = page.locator('button').filter({ hasText: /details/i }).first();
    if (await taskButton.count() > 0) {
      await taskButton.click();
      await page.waitForTimeout(1000);
      
      // Take screenshot of modal
      await expect(page).toHaveScreenshot('task-details-modal.png');
    }
  });

  test('visual comparison modal screenshot', async ({ page }) => {
    await page.goto('/admin');
    
    // Wait for page to load
    await page.waitForTimeout(1000);
    
    // Look for compare button or link
    const compareLink = page.locator('a').filter({ hasText: /compare/i }).first();
    if (await compareLink.count() > 0) {
      await compareLink.click();
      await page.waitForTimeout(1000);
      
      // Take screenshot of comparison page
      await expect(page).toHaveScreenshot('comparison-page.png');
    }
  });
});