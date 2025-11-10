import { test, expect } from '../fixtures';
import { setupDefaultMocks } from '../utils/apiMocker';

test.describe('End-to-End User Journeys', () => {
  test.beforeEach(async ({ page }) => {
    await setupDefaultMocks(page);
  });

  test('complete user journey: view dashboard → expand agent → view task details → close modal', async ({ 
    homePage, 
    taskModal 
  }) => {
    // Step 1: Load dashboard
    await homePage.goto();
    await homePage.verifyDashboardLoaded();

    // Step 2: Verify agent data is displayed
    await homePage.verifyAgentData(2);

    // Step 3: Expand first agent row
    await homePage.expandAgentRow(0);

    // Step 4: Open task details modal
    await homePage.openTaskModal(0, 0);
    await taskModal.waitForOpen();

    // Step 5: Verify modal content
    await taskModal.verifyTitle('Task Details');
    const availableTabs = await taskModal.getAvailableTabs();
    expect(availableTabs.length).toBeGreaterThan(0);

    // Step 6: Navigate through tabs
    if (availableTabs.includes('cpp_code')) {
      await taskModal.switchToTab('cpp_code');
      await taskModal.verifyCodeViewerContent('int main() { return 0; }');
    }

    // Step 7: Close modal
    await taskModal.close();
  });

  test('user refreshes data and sees updated information', async ({ page, homePage }) => {
    // Initial load
    await homePage.goto();
    await homePage.verifyDashboardLoaded();
    
    const initialRowCount = await homePage.getAgentRowCount();
    expect(initialRowCount).toBe(2);

    // Mock updated API response for refresh
    await page.route('**/api/agents**', async (route) => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          agents: [
            {
              id: 'agent-1',
              name: 'Refreshed Agent 1',
              status: 'active',
              performance: 95.0,
              totalRuns: 100,
              successRate: 0.95,
              lastRun: '2025-11-10T12:00:00Z',
              tasks: []
            }
          ]
        }),
      });
    });

    // Refresh data
    await homePage.refreshData();
    
    // Verify updated data
    const updatedRow = await homePage.getAgentRowByName('Refreshed Agent 1');
    await expect(updatedRow).toBeVisible();
    await expect(updatedRow).toContainText('95.0');
    
    const newRowCount = await homePage.getAgentRowCount();
    expect(newRowCount).toBe(1);
  });

  test('user navigates with keyboard only', async ({ page, homePage, taskModal }) => {
    await homePage.goto();
    await homePage.verifyDashboardLoaded();

    // Navigate to refresh button using keyboard
    await page.keyboard.press('Tab');
    let focusedElement = page.locator(':focus');
    
    // Keep tabbing until we reach the refresh button
    let attempts = 0;
    while (attempts < 10) {
      const text = await focusedElement.textContent();
      if (text?.toLowerCase().includes('refresh')) {
        break;
      }
      await page.keyboard.press('Tab');
      focusedElement = page.locator(':focus');
      attempts++;
    }

    // Activate refresh with Enter
    await page.keyboard.press('Enter');
    await homePage.verifyDashboardLoaded();

    // Navigate to first agent row and expand it
    await page.keyboard.press('Tab');
    focusedElement = page.locator(':focus');
    
    // If it's an agent row, expand it
    if (await focusedElement.locator('td').count() > 0) {
      await page.keyboard.press('Enter');
      
      // Navigate to view logs button if available
      await page.keyboard.press('Tab');
      focusedElement = page.locator(':focus');
      
      const text = await focusedElement.textContent();
      if (text?.toLowerCase().includes('view logs')) {
        await page.keyboard.press('Enter');
        await taskModal.waitForOpen();
        
        // Close modal with Escape
        await taskModal.closeByEscape();
      }
    }
  });
});

test.describe('Performance and Load Tests', () => {
  test('dashboard should handle large datasets efficiently', async ({ page, homePage }) => {
    // Mock large dataset
    const largeDataset = {
      agents: Array.from({ length: 100 }, (_, i) => ({
        id: `agent-${i}`,
        name: `Agent ${i}`,
        status: i % 2 === 0 ? 'active' : 'idle',
        performance: Math.random() * 100,
        totalRuns: Math.floor(Math.random() * 1000),
        successRate: Math.random(),
        lastRun: '2025-11-10T10:00:00Z',
        tasks: Array.from({ length: Math.floor(Math.random() * 10) }, (_, j) => ({
          id: `task-${i}-${j}`,
          name: `Task ${i}-${j}`,
          status: 'completed',
          duration: Math.floor(Math.random() * 5000),
          cpp_code: `int function${i}_${j}() { return ${i + j}; }`,
          logs: [`Task ${i}-${j} log`]
        }))
      }))
    };

    await page.route('**/api/agents**', async (route) => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify(largeDataset),
      });
    });

    const startTime = Date.now();
    await homePage.goto();
    await homePage.verifyDashboardLoaded();
    const loadTime = Date.now() - startTime;

    // Even with 100 agents, should load within 5 seconds
    expect(loadTime).toBeLessThan(5000);
    
    // Verify all agents are displayed
    await homePage.verifyAgentData(100);
  });

  test('should maintain performance when opening/closing modals rapidly', async ({ 
    homePage, 
    taskModal 
  }) => {
    await homePage.goto();
    await homePage.verifyDashboardLoaded();

    // Rapidly open and close modal multiple times
    for (let i = 0; i < 5; i++) {
      await homePage.openTaskModal(0, 0);
      await taskModal.waitForOpen();
      await taskModal.close();
    }

    // Dashboard should still be responsive
    await homePage.verifyDashboardLoaded();
    await homePage.refreshData();
  });
});