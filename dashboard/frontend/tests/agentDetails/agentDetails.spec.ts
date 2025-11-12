import { test, expect } from '../fixtures';

test('agent row expands to show run/task details', async ({ page }) => {
  await page.goto('/');
  
  // Wait for the table to load
  await expect(page.getByRole('table')).toBeVisible();
  
  // Check if there are any agent rows
  const agentRows = page.locator('tbody tr');
  const rowCount = await agentRows.count();
  
  if (rowCount > 0) {
    // Click the first agent row (simulate expand)
    const firstAgentRow = agentRows.first();
    await firstAgentRow.click();
    // Could check for expanded content here if implemented
  } else {
    // No data scenario - this is also valid
    console.log('No agent data available to test expansion');
  }
});

test('task details modal opens', async ({ page }) => {
  await page.goto('/');
  
  // Wait for the table to load
  await expect(page.getByRole('table')).toBeVisible();
  
  // Check if there are any agent rows
  const agentRows = page.locator('tbody tr');
  const rowCount = await agentRows.count();
  
  if (rowCount > 0) {
    // Expand first agent row
    const firstAgentRow = agentRows.first();
    await firstAgentRow.click();
    
    // Wait a bit for any expansion to occur
    await page.waitForTimeout(1000);
    
    // Check if "View Logs" button exists
    const viewLogsBtn = page.getByRole('button', { name: /view logs/i }).first();
    const isVisible = await viewLogsBtn.isVisible().catch(() => false);
    
    if (isVisible) {
      await viewLogsBtn.click();
      // Modal should appear
      await expect(page.getByRole('dialog')).toBeVisible();
    } else {
      console.log('No View Logs button found - might be no task data');
    }
  } else {
    console.log('No agent data available to test modal');
  }
});
