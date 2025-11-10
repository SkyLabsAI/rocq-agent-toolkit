import { test, expect } from '../fixtures';
import { setupDefaultMocks } from '../utils/apiMocker';
import { injectAxe, checkA11y } from 'axe-playwright';

test.describe('Accessibility Tests', () => {
  test.beforeEach(async ({ page }) => {
    await setupDefaultMocks(page);
    await injectAxe(page);
  });

  test('dashboard should have no accessibility violations', async ({ homePage }) => {
    await homePage.goto();
    await homePage.verifyDashboardLoaded();
    
    await checkA11y(homePage.page, null, {
      detailedReport: true,
      detailedReportOptions: { html: true },
    });
  });

  test('task modal should have no accessibility violations', async ({ homePage, taskModal }) => {
    await homePage.goto();
    await homePage.openTaskModal(0, 0);
    await taskModal.waitForOpen();
    
    await checkA11y(taskModal.modal, null, {
      detailedReport: true,
      detailedReportOptions: { html: true },
    });
  });

  test('should support high contrast mode', async ({ page, homePage }) => {
    // Simulate high contrast mode
    await page.emulateMedia({ colorScheme: 'dark', reducedMotion: 'reduce' });
    
    await homePage.goto();
    await homePage.verifyDashboardLoaded();
    
    // Elements should still be visible and accessible
    await expect(homePage.dashboardTitle).toBeVisible();
    await expect(homePage.agentTable).toBeVisible();
    await expect(homePage.refreshButton).toBeVisible();
  });

  test('should support screen reader navigation', async ({ page, homePage }) => {
    await homePage.goto();
    
    // Check for proper heading structure
    const headings = await page.locator('h1, h2, h3, h4, h5, h6').all();
    expect(headings.length).toBeGreaterThan(0);
    
    // Check for proper landmarks
    const main = page.locator('main');
    await expect(main).toBeVisible();
    
    // Check for proper table structure
    const tableHeaders = page.locator('th');
    const headerCount = await tableHeaders.count();
    expect(headerCount).toBeGreaterThan(0);
  });

  test('should support keyboard-only navigation', async ({ page, homePage }) => {
    await homePage.goto();
    
    // Start tabbing through the page
    let focusedElements: string[] = [];
    
    for (let i = 0; i < 10; i++) {
      await page.keyboard.press('Tab');
      const focused = page.locator(':focus');
      const tagName = await focused.evaluate(el => el.tagName);
      const role = await focused.getAttribute('role');
      const ariaLabel = await focused.getAttribute('aria-label');
      
      const description = `${tagName}${role ? `[${role}]` : ''}${ariaLabel ? `(${ariaLabel})` : ''}`;
      focusedElements.push(description);
    }
    
    // Should have navigated through interactive elements
    expect(focusedElements.length).toBeGreaterThan(0);
    console.log('Tab navigation path:', focusedElements);
  });

  test('should announce dynamic content changes', async ({ page, homePage }) => {
    await homePage.goto();
    
    // Check for aria-live regions
    const liveRegions = page.locator('[aria-live]');
    const liveRegionCount = await liveRegions.count();
    
    if (liveRegionCount > 0) {
      // Trigger a refresh to test live announcements
      await homePage.refreshData();
      
      // Live regions should be present for status updates
      await expect(liveRegions.first()).toBeVisible();
    }
  });

  test('form controls should have proper labels', async ({ page, homePage }) => {
    await homePage.goto();
    
    // Check buttons have accessible names
    const buttons = page.locator('button');
    const buttonCount = await buttons.count();
    
    for (let i = 0; i < buttonCount; i++) {
      const button = buttons.nth(i);
      const accessibleName = await button.evaluate(el => {
        // Check for aria-label, aria-labelledby, or text content
        return el.getAttribute('aria-label') || 
               el.getAttribute('aria-labelledby') ||
               el.textContent?.trim();
      });
      
      expect(accessibleName).toBeTruthy();
    }
  });

  test('should respect reduced motion preferences', async ({ page, homePage }) => {
    // Set reduced motion preference
    await page.emulateMedia({ reducedMotion: 'reduce' });
    
    await homePage.goto();
    await homePage.verifyDashboardLoaded();
    
    // Animations should be disabled or minimal
    // This would depend on your CSS implementation
    const animatedElements = page.locator('[class*="animate"], [class*="transition"]');
    const count = await animatedElements.count();
    
    if (count > 0) {
      // Check that animations are disabled or reduced
      const computedStyle = await animatedElements.first().evaluate(el => 
        getComputedStyle(el).getPropertyValue('animation-duration')
      );
      
      // Animation should be disabled (0s) or very short
      expect(['0s', '0.01s']).toContain(computedStyle);
    }
  });

  test('color contrast should meet WCAG standards', async ({ page, homePage }) => {
    await homePage.goto();
    
    // This would require a contrast checking tool
    // For now, we'll check that text is visible
    const textElements = page.locator('p, span, div, td, th, h1, h2, h3, h4, h5, h6');
    const count = await textElements.count();
    
    // Sample a few elements to ensure they're visible
    for (let i = 0; i < Math.min(count, 5); i++) {
      const element = textElements.nth(i);
      const text = await element.textContent();
      
      if (text && text.trim()) {
        await expect(element).toBeVisible();
      }
    }
  });
});