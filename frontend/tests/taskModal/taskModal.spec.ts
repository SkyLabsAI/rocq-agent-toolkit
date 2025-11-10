import { test, expect } from '../fixtures';
import { setupDefaultMocks, ApiMocker } from '../utils/apiMocker';

test.describe('Task Details Modal', () => {
  test.beforeEach(async ({ page }) => {
    await setupDefaultMocks(page);
  });

  test('should open modal when clicking view logs button', async ({ homePage, taskModal }) => {
    await homePage.goto();
    await homePage.openTaskModal(0, 0);
    
    await taskModal.waitForOpen();
    await taskModal.verifyTitle('Task Details');
  });

  test('should close modal with close button', async ({ homePage, taskModal }) => {
    await homePage.goto();
    await homePage.openTaskModal(0, 0);
    
    await taskModal.waitForOpen();
    await taskModal.close();
  });

  test('should close modal with Escape key', async ({ homePage, taskModal }) => {
    await homePage.goto();
    await homePage.openTaskModal(0, 0);
    
    await taskModal.waitForOpen();
    await taskModal.closeByEscape();
  });

  test('should display different tabs based on available data', async ({ homePage, taskModal }) => {
    await homePage.goto();
    await homePage.openTaskModal(0, 0);
    
    await taskModal.waitForOpen();
    
    const availableTabs = await taskModal.getAvailableTabs();
    expect(availableTabs.length).toBeGreaterThan(0);
    
    // Should have cpp_code tab based on our mock data
    expect(availableTabs).toContain('cpp_code');
  });

  test('should show code viewer for cpp_code tab', async ({ homePage, taskModal }) => {
    await homePage.goto();
    await homePage.openTaskModal(0, 0);
    
    await taskModal.waitForOpen();
    await taskModal.switchToTab('cpp_code');
    
    // Should display the mocked C++ code
    await taskModal.verifyCodeViewerContent('int main() { return 0; }');
  });

  test('should switch between tabs correctly', async ({ homePage, taskModal }) => {
    await homePage.goto();
    await homePage.openTaskModal(0, 0);
    
    await taskModal.waitForOpen();
    
    const availableTabs = await taskModal.getAvailableTabs();
    
    // Test switching between all available tabs
    for (const tab of availableTabs) {
      await taskModal.switchToTab(tab);
      // Verify tab is active (this would depend on your CSS classes)
      const activeTab = taskModal.page.locator('[role="tab"][aria-selected="true"]');
      await expect(activeTab).toContainText(tab);
    }
  });

  test('should display JSON content for non-code tabs', async ({ homePage, taskModal }) => {
    await homePage.goto();
    await homePage.openTaskModal(0, 0);
    
    await taskModal.waitForOpen();
    
    // Switch to a JSON tab (like logs or other data)
    const availableTabs = await taskModal.getAvailableTabs();
    const jsonTab = availableTabs.find(tab => !['cpp_code', 'code'].includes(tab));
    
    if (jsonTab) {
      await taskModal.switchToTab(jsonTab);
      await expect(taskModal.jsonViewer).toBeVisible();
    }
  });
});

test.describe('Task Details Modal - Edge Cases', () => {
  test('should handle modal with no task data', async ({ page, homePage, taskModal }) => {
    const apiMocker = new ApiMocker(page);
    
    // Mock agent with no tasks
    const noTasksData = {
      agents: [{
        id: 'agent-1',
        name: 'Agent No Tasks',
        status: 'active',
        performance: 85.5,
        totalRuns: 0,
        successRate: 0,
        lastRun: null,
        tasks: []
      }]
    };
    
    await apiMocker.mockAgentsAPI(noTasksData);
    await homePage.goto();
    
    // Should not have any view logs buttons
    const viewLogsButtons = homePage.page.getByRole('button', { name: /view logs/i });
    await expect(viewLogsButtons).toHaveCount(0);
  });

  test('should handle modal with malformed task data', async ({ page, homePage, taskModal }) => {
    const apiMocker = new ApiMocker(page);
    
    // Mock task with minimal/malformed data
    const malformedData = {
      agents: [{
        id: 'agent-1',
        name: 'Test Agent',
        status: 'active',
        performance: 85.5,
        totalRuns: 1,
        successRate: 1,
        lastRun: '2025-11-10T10:00:00Z',
        tasks: [{
          id: 'task-1',
          name: 'Malformed Task',
          status: 'completed',
          // Missing cpp_code and other typical fields
        }]
      }]
    };
    
    await apiMocker.mockAgentsAPI(malformedData);
    await homePage.goto();
    await homePage.openTaskModal(0, 0);
    
    await taskModal.waitForOpen();
    
    // Modal should still open but handle missing data gracefully
    const availableTabs = await taskModal.getAvailableTabs();
    expect(availableTabs.length).toBeGreaterThanOrEqual(1);
  });
});

test.describe('Task Details Modal - Accessibility', () => {
  test.beforeEach(async ({ page }) => {
    await setupDefaultMocks(page);
  });

  test('should be accessible and follow ARIA patterns', async ({ homePage, taskModal }) => {
    await homePage.goto();
    await homePage.openTaskModal(0, 0);
    
    await taskModal.waitForOpen();
    await taskModal.verifyModalAccessibility();
  });

  test('should support keyboard navigation', async ({ homePage, taskModal }) => {
    await homePage.goto();
    await homePage.openTaskModal(0, 0);
    
    await taskModal.waitForOpen();
    await taskModal.verifyTabKeyNavigation();
  });

  test('should trap focus within modal', async ({ page, homePage, taskModal }) => {
    await homePage.goto();
    await homePage.openTaskModal(0, 0);
    
    await taskModal.waitForOpen();
    
    // Focus should be within the modal
    const focusedElement = page.locator(':focus');
    const modalContent = taskModal.modal;
    
    // The focused element should be inside the modal
    await expect(modalContent).toContainText(await focusedElement.textContent() || '');
  });
});

test.describe('Task Details Modal - Visual Tests', () => {
  test.beforeEach(async ({ page }) => {
    await setupDefaultMocks(page);
  });

  test('should match visual baseline - modal with code', async ({ page, homePage, taskModal }) => {
    await homePage.goto();
    await homePage.openTaskModal(0, 0);
    
    await taskModal.waitForOpen();
    await taskModal.switchToTab('cpp_code');
    
    // Wait for syntax highlighting to load
    await page.waitForTimeout(500);
    
    await expect(taskModal.modal).toHaveScreenshot('task-modal-with-code.png');
  });

  test('should match visual baseline - modal with JSON', async ({ page, homePage, taskModal }) => {
    await homePage.goto();
    await homePage.openTaskModal(0, 0);
    
    await taskModal.waitForOpen();
    
    // Switch to first non-code tab
    const availableTabs = await taskModal.getAvailableTabs();
    const jsonTab = availableTabs.find(tab => !['cpp_code', 'code'].includes(tab));
    
    if (jsonTab) {
      await taskModal.switchToTab(jsonTab);
      await expect(taskModal.modal).toHaveScreenshot('task-modal-with-json.png');
    }
  });
});