import { Page, expect } from '@playwright/test';
import AxeBuilder from '@axe-core/playwright';

/**
 * Wait for the page to be fully loaded
 */
export async function waitForPageLoad(page: Page) {
  await page.waitForLoadState('domcontentloaded');
  await page.waitForLoadState('networkidle');
}

/**
 * Wait for an element to be visible
 */
export async function waitForElement(
  page: Page,
  selector: string,
  timeout = 10000
) {
  await page.waitForSelector(selector, { state: 'visible', timeout });
}

/**
 * Check if an element is visible
 */
export async function isElementVisible(
  page: Page,
  selector: string
): Promise<boolean> {
  try {
    const element = await page.locator(selector);
    return await element.isVisible();
  } catch {
    return false;
  }
}

/**
 * Run accessibility checks on the page
 */
export async function checkAccessibility(
  page: Page,
  options?: {
    detailedReport?: boolean;
    detailedReportOptions?: { html?: boolean };
  }
) {
  const accessibilityScanResults = await new AxeBuilder({ page }).analyze();

  // Assert that there are no accessibility violations
  expect(accessibilityScanResults.violations).toEqual([]);

  return accessibilityScanResults;
}

/**
 * Run accessibility checks with custom rules
 */
export async function checkAccessibilityWithRules(
  page: Page,
  rulesToRun: string[]
) {
  const accessibilityScanResults = await new AxeBuilder({ page })
    .withRules(rulesToRun)
    .analyze();

  expect(accessibilityScanResults.violations).toEqual([]);

  return accessibilityScanResults;
}

/**
 * Wait for navigation to complete
 */
export async function waitForNavigation(page: Page, expectedUrl: string) {
  await page.waitForURL(expectedUrl);
  await waitForPageLoad(page);
}

/**
 * Get text content of an element
 */
export async function getElementText(
  page: Page,
  selector: string
): Promise<string> {
  const element = await page.locator(selector);
  return (await element.textContent()) || '';
}

/**
 * Click and wait for navigation
 */
export async function clickAndWaitForNavigation(
  page: Page,
  selector: string,
  expectedUrlPattern?: string | RegExp
) {
  await Promise.all([
    expectedUrlPattern
      ? page.waitForURL(expectedUrlPattern)
      : page.waitForLoadState('networkidle'),
    page.click(selector),
  ]);
}

/**
 * Take a full page screenshot
 */
export async function takeFullPageScreenshot(page: Page, name: string) {
  await page.screenshot({ path: `screenshots/${name}.png`, fullPage: true });
}

/**
 * Check if element has specific class
 */
export async function hasClass(
  page: Page,
  selector: string,
  className: string
): Promise<boolean> {
  const element = await page.locator(selector);
  const classes = await element.getAttribute('class');
  return classes ? classes.split(' ').includes(className) : false;
}
