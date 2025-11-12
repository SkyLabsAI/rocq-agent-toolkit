import { test, expect } from './fixtures';

test.describe('Basic Setup Test', () => {
  test('should be able to visit a simple page', async ({ page }) => {
    // Visit Google as a basic test
    await page.goto('https://www.google.com');
    await expect(page).toHaveTitle(/Google/);
  });

  test('should verify Playwright setup', async ({ page }) => {
    // Test basic Playwright functionality
    await page.goto('data:text/html,<html><body><h1>Test Page</h1></body></html>');
    await expect(page.locator('h1')).toHaveText('Test Page');
  });
});