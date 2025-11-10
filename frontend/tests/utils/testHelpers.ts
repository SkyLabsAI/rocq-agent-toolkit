import { Page, Locator } from '@playwright/test';

/**
 * Wait for element to be stable (not moving/changing)
 */
export async function waitForElementStable(element: Locator, timeout = 3000): Promise<void> {
  let previousBox = await element.boundingBox();
  const startTime = Date.now();
  
  while (Date.now() - startTime < timeout) {
    await new Promise(resolve => setTimeout(resolve, 100));
    const currentBox = await element.boundingBox();
    
    if (previousBox && currentBox &&
        previousBox.x === currentBox.x &&
        previousBox.y === currentBox.y &&
        previousBox.width === currentBox.width &&
        previousBox.height === currentBox.height) {
      return;
    }
    
    previousBox = currentBox;
  }
}

/**
 * Take a screenshot with consistent settings
 */
export async function takeScreenshot(
  page: Page, 
  name: string, 
  options: { fullPage?: boolean; clip?: { x: number; y: number; width: number; height: number } } = {}
) {
  // Wait for animations to complete
  await page.waitForTimeout(300);
  
  // Disable animations for consistent screenshots
  await page.addStyleTag({
    content: `
      *, *::before, *::after {
        animation-duration: 0s !important;
        animation-delay: 0s !important;
        transition-duration: 0s !important;
        transition-delay: 0s !important;
      }
    `
  });
  
  return await page.screenshot({
    path: `test-results/screenshots/${name}`,
    fullPage: options.fullPage,
    clip: options.clip
  });
}

/**
 * Measure page load performance
 */
export async function measurePageLoad(page: Page): Promise<{
  domContentLoaded: number;
  load: number;
  firstContentfulPaint: number;
}> {
  const metrics = await page.evaluate(() => ({
    domContentLoaded: performance.timing.domContentLoadedEventEnd - performance.timing.navigationStart,
    load: performance.timing.loadEventEnd - performance.timing.navigationStart,
    firstContentfulPaint: performance.getEntriesByName('first-contentful-paint')[0]?.startTime || 0
  }));
  
  return metrics;
}

/**
 * Wait for network to be idle
 */
export async function waitForNetworkIdle(page: Page, timeout = 5000): Promise<void> {
  await page.waitForLoadState('networkidle', { timeout });
}

/**
 * Get all console messages during a test
 */
export function collectConsoleMessages(page: Page): { type: string; text: string; timestamp: number }[] {
  const messages: { type: string; text: string; timestamp: number }[] = [];
  
  page.on('console', msg => {
    messages.push({
      type: msg.type(),
      text: msg.text(),
      timestamp: Date.now()
    });
  });
  
  return messages;
}

/**
 * Check for JavaScript errors
 */
export function collectJavaScriptErrors(page: Page): Error[] {
  const errors: Error[] = [];
  
  page.on('pageerror', error => {
    errors.push(error);
  });
  
  return errors;
}

/**
 * Simulate slow network conditions
 */
export async function simulateSlowNetwork(page: Page): Promise<void> {
  await page.route('**/*', async route => {
    await new Promise(resolve => setTimeout(resolve, 1000)); // 1 second delay
    await route.continue();
  });
}

/**
 * Clear all browser storage
 */
export async function clearBrowserStorage(page: Page): Promise<void> {
  await page.evaluate(() => {
    localStorage.clear();
    sessionStorage.clear();
  });
  
  // Clear cookies
  const context = page.context();
  await context.clearCookies();
}

/**
 * Set viewport for mobile testing
 */
export async function setMobileViewport(page: Page): Promise<void> {
  await page.setViewportSize({ width: 375, height: 667 }); // iPhone SE size
}

/**
 * Check if element is in viewport
 */
export async function isElementInViewport(element: Locator): Promise<boolean> {
  return await element.evaluate(el => {
    const rect = el.getBoundingClientRect();
    return (
      rect.top >= 0 &&
      rect.left >= 0 &&
      rect.bottom <= (window.innerHeight || document.documentElement.clientHeight) &&
      rect.right <= (window.innerWidth || document.documentElement.clientWidth)
    );
  });
}

/**
 * Scroll element into view
 */
export async function scrollIntoView(element: Locator): Promise<void> {
  await element.scrollIntoViewIfNeeded();
  await new Promise(resolve => setTimeout(resolve, 100)); // Brief pause after scroll
}

/**
 * Generate random test data
 */
export function generateMockAgent(id: string) {
  return {
    id,
    name: `Test Agent ${id}`,
    status: Math.random() > 0.5 ? 'active' : 'idle',
    performance: Math.round(Math.random() * 100 * 100) / 100, // 2 decimal places
    totalRuns: Math.floor(Math.random() * 100),
    successRate: Math.round(Math.random() * 100) / 100, // 0-1 range
    lastRun: new Date().toISOString(),
    tasks: Array.from({ length: Math.floor(Math.random() * 5) }, (_, i) => ({
      id: `task-${id}-${i}`,
      name: `Task ${id}-${i}`,
      status: Math.random() > 0.8 ? 'failed' : 'completed',
      duration: Math.floor(Math.random() * 5000),
      cpp_code: `int function_${id}_${i}() { return ${Math.floor(Math.random() * 100)}; }`,
      logs: [`Task ${id}-${i} started`, `Task ${id}-${i} completed`]
    }))
  };
}

/**
 * Wait for specific text to appear anywhere on page
 */
export async function waitForText(page: Page, text: string, timeout = 5000): Promise<void> {
  await page.waitForFunction(
    (searchText) => document.body.textContent?.includes(searchText),
    text,
    { timeout }
  );
}