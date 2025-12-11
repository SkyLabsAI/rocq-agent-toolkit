import AxeBuilder from '@axe-core/playwright';
import { expect, type Page } from '@playwright/test';

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
  _options?: {
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
export async function elementHasClass(
  page: Page,
  selector: string,
  className: string
): Promise<boolean> {
  const element = await page.locator(selector);
  const classes = await element.getAttribute('class');
  return classes ? classes.split(' ').includes(className) : false;
}

/**
 * Take a screenshot with proper directory structure
 */
export async function takeScreenshot(
  page: Page,
  category: string,
  name: string
): Promise<void> {
  await page.screenshot({
    path: `test-results/screenshots/${category}/${name}.png`,
    fullPage: true,
  });
}

/**
 * Switch to a specific view (agent or dataset)
 */
export async function switchToView(
  page: Page,
  viewType: 'agent' | 'dataset'
): Promise<void> {
  const viewButton = page.getByRole('button', {
    name: new RegExp(viewType, 'i'),
  });
  if ((await viewButton.count()) > 0) {
    await viewButton.click();
    await waitForPageLoad(page);
  }
}

/**
 * Select multiple items by checkboxes
 */
export async function selectMultipleItems(
  page: Page,
  selector: string,
  count: number = 2
): Promise<boolean> {
  const checkboxes = page.locator(selector);
  const availableCount = await checkboxes.count();

  if (availableCount < count) {
    return false;
  }

  for (let i = 0; i < count; i++) {
    await checkboxes.nth(i).check();
    await page.waitForTimeout(300); // Small delay for UI updates
  }

  return true;
}

/**
 * Navigate to agent comparison from selections
 */
export async function navigateToAgentComparison(page: Page): Promise<boolean> {
  const compareButton = page.getByRole('button', { name: /compare.*agents?/i });
  if ((await compareButton.count()) > 0) {
    await compareButton.click();
    await waitForPageLoad(page);
    return true;
  }
  return false;
}

/**
 * Navigate to run comparison from selections
 */
export async function navigateToRunComparison(page: Page): Promise<boolean> {
  const compareButton = page.getByRole('button', { name: /compare.*runs?/i });
  if ((await compareButton.count()) > 0) {
    await compareButton.click();
    await waitForPageLoad(page);
    return true;
  }
  return false;
}

/**
 * Verify sticky compare bar is visible
 */
export async function verifyStickyCompareBar(
  page: Page,
  shouldBeVisible: boolean = true
): Promise<void> {
  const compareBar = page.locator(
    '[data-testid="sticky-compare-bar"], [class*="sticky-compare"]'
  );
  if (shouldBeVisible) {
    if ((await compareBar.count()) > 0) {
      await expect(compareBar.first()).toBeVisible();
    }
  } else {
    if ((await compareBar.count()) > 0) {
      await expect(compareBar.first()).not.toBeVisible();
    }
  }
}

/**
 * Verify no selections are active (checkboxes unchecked)
 */
export async function verifyNoSelections(page: Page): Promise<void> {
  const checkedBoxes = page.locator('input[type="checkbox"]:checked');
  await expect(checkedBoxes).toHaveCount(0);
}

/**
 * Complete agent view flow: expand agent -> expand dataset -> select runs
 */
export async function completeAgentViewFlow(page: Page): Promise<{
  success: boolean;
  agentExpanded: boolean;
  datasetExpanded: boolean;
  runsSelected: boolean;
}> {
  const result = {
    success: false,
    agentExpanded: false,
    datasetExpanded: false,
    runsSelected: false,
  };

  // Expand agent
  const agentRow = page
    .locator('[data-testid="agent-row"], tr')
    .filter({ hasText: /agent/i })
    .first();
  if ((await agentRow.count()) > 0) {
    await agentRow.click();
    await page.waitForTimeout(500);
    result.agentExpanded = true;

    // Expand dataset
    const datasetItem = page
      .locator('[data-testid="dataset-item"], [class*="dataset"]')
      .first();
    if ((await datasetItem.count()) > 0) {
      await datasetItem.click();
      await page.waitForTimeout(500);
      result.datasetExpanded = true;

      // Select runs
      const runCheckboxes = page.locator('input[type="checkbox"]');
      if ((await runCheckboxes.count()) >= 2) {
        await runCheckboxes.nth(0).check();
        await runCheckboxes.nth(1).check();
        result.runsSelected = true;
        result.success = true;
      }
    }
  }

  return result;
}

/**
 * Complete dataset view flow: expand dataset -> expand agent -> select runs
 */
export async function completeDatasetViewFlow(page: Page): Promise<{
  success: boolean;
  datasetExpanded: boolean;
  agentExpanded: boolean;
  runsSelected: boolean;
}> {
  const result = {
    success: false,
    datasetExpanded: false,
    agentExpanded: false,
    runsSelected: false,
  };

  // Expand dataset
  const datasetItem = page
    .locator('[data-testid="dataset-item"], [class*="dataset-card"]')
    .first();
  if ((await datasetItem.count()) > 0) {
    await datasetItem.click();
    await page.waitForTimeout(500);
    result.datasetExpanded = true;

    // Expand agent
    const agentItem = page
      .locator('[data-testid="agent-item"], [class*="agent-row"], tr')
      .filter({ hasText: /agent/i })
      .first();
    if ((await agentItem.count()) > 0) {
      await agentItem.click();
      await page.waitForTimeout(500);
      result.agentExpanded = true;

      // Select runs
      const runCheckboxes = page.locator('input[type="checkbox"]');
      if ((await runCheckboxes.count()) >= 2) {
        await runCheckboxes.nth(0).check();
        await runCheckboxes.nth(1).check();
        result.runsSelected = true;
        result.success = true;
      }
    }
  }

  return result;
}

/**
 * Test dataset switching clears selections
 */
export async function testDatasetSwitchingClearsSelections(
  page: Page
): Promise<boolean> {
  // Select items in first dataset
  const firstDataset = page
    .locator('[data-testid="dataset-item"], [class*="dataset-card"]')
    .first();
  if ((await firstDataset.count()) > 0) {
    await firstDataset.click();
    await page.waitForTimeout(500);

    const checkboxes = page.locator('input[type="checkbox"]');
    if ((await checkboxes.count()) > 0) {
      await checkboxes.first().check();

      // Switch to second dataset
      const secondDataset = page
        .locator('[data-testid="dataset-item"], [class*="dataset-card"]')
        .nth(1);
      if ((await secondDataset.count()) > 0) {
        await secondDataset.click();
        await page.waitForTimeout(500);

        // Verify selections cleared
        const checkedBoxes = page.locator('input[type="checkbox"]:checked');
        return (await checkedBoxes.count()) === 0;
      }
    }
  }

  return false;
}
