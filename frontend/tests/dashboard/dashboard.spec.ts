import { test, expect } from '../fixtures';
import { setupDefaultMocks, ApiMocker } from '../utils/apiMocker';

test.describe('Dashboard Core Functionality', () => {
  test.beforeEach(async ({ page }) => {
    await setupDefaultMocks(page);
  });

  test('should load dashboard with agent performance data', async ({ homePage }) => {
    await homePage.goto();
    await homePage.verifyDashboardLoaded();
    await homePage.verifyAgentData(2); // Based on our mock data
  });

  test('should refresh data when refresh button is clicked', async ({ page, homePage }) => {
    const apiMocker = new ApiMocker(page);
    
    await homePage.goto();
    await homePage.verifyDashboardLoaded();
    
    // Mock updated data for refresh
    const updatedData = {
      agents: [
        {
          id: 'agent-1',
          name: 'Updated Agent 1',
          status: 'active',
          performance: 90.0,
          totalRuns: 50,
          successRate: 0.90,
          lastRun: '2025-11-10T11:00:00Z',
          tasks: []
        }
      ]
    };
    
    await apiMocker.mockAgentsAPI(updatedData);
    await homePage.refreshData();
    
    // Verify updated data is displayed
    const updatedRow = await homePage.getAgentRowByName('Updated Agent 1');
    await expect(updatedRow).toBeVisible();
  });

  test('should handle empty data gracefully', async ({ page, homePage }) => {
    const apiMocker = new ApiMocker(page);
    await apiMocker.mockEmptyAgentsAPI();
    
    await homePage.goto();
    await homePage.verifyEmptyState();
  });

  test('should handle API errors gracefully', async ({ page, homePage }) => {
    const apiMocker = new ApiMocker(page);
    await apiMocker.mockAgentsAPIError(500, 'Server unavailable');
    
    await homePage.goto();
    
    // Verify error state is shown
    await expect(homePage.errorMessage).toBeVisible();
    await expect(homePage.errorMessage).toContainText('Server unavailable');
  });
});

test.describe('Dashboard Performance', () => {
  test('should load within acceptable time', async ({ page, homePage }) => {
    await setupDefaultMocks(page);
    
    const startTime = Date.now();
    await homePage.goto();
    const loadTime = Date.now() - startTime;
    
    // Dashboard should load within 3 seconds
    expect(loadTime).toBeLessThan(3000);
    
    // Verify content is actually loaded
    await homePage.verifyDashboardLoaded();
  });

  test('should show loading state for slow API', async ({ page, homePage }) => {
    const apiMocker = new ApiMocker(page);
    await apiMocker.mockSlowAPI(1000);
    
    await page.goto('/');
    
    // Loading spinner should be visible initially
    await expect(homePage.loadingSpinner).toBeVisible();
    
    // After API response, content should be visible
    await homePage.verifyDashboardLoaded();
    await expect(homePage.loadingSpinner).not.toBeVisible();
  });
});

test.describe('Dashboard Accessibility', () => {
  test.beforeEach(async ({ page }) => {
    await setupDefaultMocks(page);
  });

  test('should be navigable with keyboard', async ({ page, homePage }) => {
    await homePage.goto();
    
    // Test tab navigation
    await page.keyboard.press('Tab');
    let focusedElement = page.locator(':focus');
    await expect(focusedElement).toBeVisible();
    
    // Should be able to reach refresh button
    while (await focusedElement.textContent() !== 'Refresh Data') {
      await page.keyboard.press('Tab');
      focusedElement = page.locator(':focus');
    }
    
    // Should be able to activate refresh button with Enter
    await page.keyboard.press('Enter');
    await homePage.verifyDashboardLoaded();
  });

  test('should have proper ARIA labels and roles', async ({ page, homePage }) => {
    await homePage.goto();
    
    // Check table accessibility
    await expect(homePage.agentTable).toHaveAttribute('role', 'table');
    
    // Check button accessibility
    await expect(homePage.refreshButton).toHaveAttribute('type', 'button');
    
    // Check heading structure
    await expect(homePage.dashboardTitle).toHaveRole('heading');
  });
});

test.describe('Dashboard Visual Regression', () => {
  test.beforeEach(async ({ page }) => {
    await setupDefaultMocks(page);
  });

  test('should match visual baseline - dashboard with data', async ({ page, homePage }) => {
    await homePage.goto();
    await homePage.verifyDashboardLoaded();
    
    // Wait for any animations to complete
    await page.waitForTimeout(500);
    
    await expect(page).toHaveScreenshot('dashboard-with-data.png');
  });

  test('should match visual baseline - empty state', async ({ page, homePage }) => {
    const apiMocker = new ApiMocker(page);
    await apiMocker.mockEmptyAgentsAPI();
    
    await homePage.goto();
    await homePage.verifyEmptyState();
    
    await expect(page).toHaveScreenshot('dashboard-empty-state.png');
  });
});