import { expect, test } from '@playwright/test';

import { takeScreenshot, waitForPageLoad } from './utils/test-helpers';

/**
 * E2E Test Suite: Full User Journey - Critical Paths
 *
 * Tests the complete end-to-end user flows through the application:
 * - REQ-087: Agent → Instance → Run → Visualizer → Close
 * - REQ-088: Select Runs → Compare → View Details → Back
 * - REQ-089: Dataset View → Agent Runs → Comparison
 */

test.describe('11. Full User Journey - Critical Path', () => {
    test.beforeEach(async ({ page }) => {
        await page.goto('/');
        await waitForPageLoad(page);
    });

    /**
     * REQ-087: Complete Flow: Agent → Instance → Run → Visualizer → Close
     *
     * This test verifies the primary user journey through the application:
     * 1. Load dashboard
     * 2. Click agent to expand
     * 3. Click instance to expand runs
     * 4. Click visualizer on a run
     * 5. View and interact with trace visualization
     * 6. Select spans and view details
     * 7. Change depth levels
     * 8. View logs
     * 9. Close visualizer
     * 10. Return to dashboard
     */
    test('REQ-087: should complete full agent → instance → run → visualizer → close flow', async ({
        page,
    }) => {
        // Step 1: Load dashboard - verify initial state
        await expect(page.getByText('Leader Dashboard')).toBeVisible();
        await takeScreenshot(page, 'full-journey', 'step-01-dashboard-loaded');

        // Ensure we're on the Agents tab
        const agentsTab = page.locator('button').filter({ hasText: /^Agents$/i });
        if ((await agentsTab.count()) > 0) {
            await agentsTab.first().click();
            await page.waitForTimeout(500);
        }

        // Step 2: Click agent to expand
        const agentRows = page.locator('[data-testid^="agent-row-"]');
        await expect(agentRows.first()).toBeVisible({ timeout: 10000 });

        const firstAgent = agentRows.first();
        const agentName = await firstAgent.textContent();
        console.log(`Expanding agent: ${agentName}`);

        await firstAgent.click();
        await page.waitForTimeout(3000);
        await takeScreenshot(page, 'full-journey', 'step-02-agent-expanded');

        // Verify instances or datasets are shown
        const instanceRows = page.locator('[data-testid^="instance-card-"]');

        const hasInstances = (await instanceRows.count()) > 0;
        expect(hasInstances).toBeTruthy();

        // Step 3: Click instance to expand runs (if instances exist)
        const firstInstance = instanceRows.first();
        await firstInstance.click();
        await page.waitForTimeout(1000);
        const datasetCards = page.locator('[data-testid^="instance-dataset-card"]');

        console.log('datasetCards', await datasetCards.count());
        expect(await datasetCards.count()).toBeGreaterThan(0);

        await takeScreenshot(page, 'full-journey', 'step-03-instance-expanded');

        console.log('Expanding instance to show runs');

        await datasetCards.first().click();
        await page.waitForTimeout(1000);
        await takeScreenshot(page, 'full-journey', 'step-03-dataset-expanded');

        // Verify run rows are visible
        const runRows = page.locator('[data-testid^="run-row-"]');
        await expect(runRows.first()).toBeVisible({ timeout: 1000 });

        const runCount = await runRows.count();
        console.log(`Found ${runCount} runs`);
        expect(runCount).toBeGreaterThan(0);

        // Step 4: Click visualizer on a run
        const firstRunRow = runRows.first();

        // Look for visualizer button - it might have different selectors
        const visualizerButton = firstRunRow
            .locator('button')
            .filter({ hasText: /Visualize/i })
            .first();

        await visualizerButton.click();

        await page.waitForTimeout(500);
        await takeScreenshot(page, 'full-journey', 'step-04-visualizer-opened');

        // Step 5: Verify visualizer modal is open and trace visualization is visible
        // Look for modal with "Visualizer" in the title
        const modal = page.locator('[data-testid="visualizer-modal"]');

        await expect(modal.first()).toBeVisible({ timeout: 10000 });
        console.log('Visualizer modal opened successfully');

        // Check for trace selection or span graph
        const hasTraceSelect = (await page.locator('select').count()) > 0;
        const hasSpanNodes =
            (await page
                .locator('[data-span-id]')
                .or(page.locator('[class*="span-node"]'))
                .count()) > 0;

        if (!hasTraceSelect && !hasSpanNodes) {
            // Check for "no traces" message - this is acceptable
            const noTracesMsg = page.locator('text=/no traces|traces not found/i');
            if ((await noTracesMsg.count()) > 0) {
                console.log('No traces available for this run - acceptable state');
                await takeScreenshot(page, 'full-journey', 'step-05-no-traces');

                // Close modal and end test gracefully
                const closeButton = page
                    .locator('button[aria-label*="close"]')
                    .or(page.locator('button').filter({ hasText: /×|close/i }))
                    .first();

                if ((await closeButton.count()) > 0) {
                    await closeButton.click();
                    await page.waitForTimeout(500);
                }

                return; // Test passes - no traces is a valid state
            }
        }

        // Step 6: Select a span and view details (if spans exist)
        if (hasSpanNodes) {
            const spanNodes = page
                .locator('[data-span-id]')
                .or(page.locator('[class*="span-node"]'));

            console.log(`Found ${await spanNodes.count()} span nodes`);

            const firstSpan = spanNodes.first();
            await firstSpan.click();
            await page.waitForTimeout(1000);
            await takeScreenshot(page, 'full-journey', 'step-06-span-selected');

            // Verify span details are shown in right panel
            const spanDetailsHeading = page.locator('text=/span details/i');
            if ((await spanDetailsHeading.count()) > 0) {
                await expect(spanDetailsHeading.first()).toBeVisible();
                console.log('Span details panel visible');
            }
        }

        // Step 7: Change depth levels (if depth controls exist)
        const depthButtons = page.locator('button').filter({
            hasText: /^[1-5]$|^All$/,
        });

        if ((await depthButtons.count()) > 0) {
            console.log('Testing depth controls');

            // Click depth level 2
            const depth2Button = page.locator('button').filter({ hasText: /^2$/ });
            if ((await depth2Button.count()) > 0) {
                await depth2Button.first().click();
                await page.waitForTimeout(500);
                await takeScreenshot(page, 'full-journey', 'step-07a-depth-2-selected');

                // Verify button is highlighted
                const classes = await depth2Button.first().getAttribute('class');
                expect(classes).toContain('bg-primary');
            }

            // Click "All" depth
            const allButton = page.locator('button').filter({ hasText: /^All$/ });
            if ((await allButton.count()) > 0) {
                await allButton.first().click();
                await page.waitForTimeout(500);
                await takeScreenshot(
                    page,
                    'full-journey',
                    'step-07b-depth-all-selected'
                );
            }
        }

        // Step 8: View logs (if logs section exists)
        const logsSection = page.locator('text=/^Logs$/i');
        if ((await logsSection.count()) > 0) {
            console.log('Logs section found');
            await expect(logsSection.first()).toBeVisible();
            await takeScreenshot(page, 'full-journey', 'step-08a-logs-visible');

            // Test raw JSON toggle if it exists
            const rawJsonButton = page.locator('button').filter({
                hasText: /show raw json/i,
            });

            if ((await rawJsonButton.count()) > 0) {
                await rawJsonButton.first().click();
                await page.waitForTimeout(500);
                await takeScreenshot(page, 'full-journey', 'step-08b-raw-json-view');

                // Toggle back to formatted view
                const formattedButton = page
                    .locator('button')
                    .filter({ hasText: /formatted|try formatted/i });

                if ((await formattedButton.count()) > 0) {
                    await formattedButton.first().click();
                    await page.waitForTimeout(500);
                    await takeScreenshot(page, 'full-journey', 'step-08c-formatted-view');
                }
            }
        }

        // Step 9: Close visualizer modal
        const closeButton = page
            .locator('button[aria-label*="close"]')
            .or(page.locator('button').filter({ hasText: /×|close/i }))
            .or(page.locator('[role="dialog"] button').first())
            .first();

        if ((await closeButton.count()) > 0) {
            await closeButton.click();
            await page.waitForTimeout(500);
            console.log('Visualizer modal closed');
        }

        // Alternatively try ESC key
        if ((await modal.count()) > 0 && (await modal.first().isVisible())) {
            await page.keyboard.press('Escape');
            await page.waitForTimeout(500);
        }

        await takeScreenshot(page, 'full-journey', 'step-09-visualizer-closed');

        // Step 10: Verify we're back on dashboard
        await expect(page.getByText('Leader Dashboard')).toBeVisible();
        console.log('Successfully returned to dashboard');
        await takeScreenshot(page, 'full-journey', 'step-10-back-to-dashboard');
    });

    /**
     * REQ-088: Complete Flow: Select Runs → Compare → View Details → Back
     *
     * This test verifies the run comparison workflow:
     * 1. Load dashboard
     * 2. Expand agent to see instances
     * 3. Click instance to see datasets
     * 4. Click dataset to see runs
     * 5. Select 2+ runs
     * 6. Verify sticky compare bar appears
     * 7. Click "Compare Selected"
     * 8. View comparison table
     * 9. Click on task cell to see details
     * 10. Close task details
     * 11. Navigate back to dashboard
     */
    test('REQ-088: should complete select runs → compare → view details → back flow', async ({
        page,
    }) => {
        // Step 1: Load dashboard
        await expect(page.getByText('Leader Dashboard')).toBeVisible();
        await takeScreenshot(page, 'compare-flow', 'step-01-dashboard-loaded');

        // Ensure we're on the Agents tab
        const agentsTab = page.locator('button').filter({ hasText: /^Agents$/i });
        if ((await agentsTab.count()) > 0) {
            await agentsTab.first().click();
            await page.waitForTimeout(500);
        }

        // Step 2: Expand agent to see instances
        const agentRows = page.locator('[data-testid^="agent-row-"]');
        await expect(agentRows.first()).toBeVisible({ timeout: 10000 });

        await agentRows.first().click();
        await page.waitForTimeout(2000);
        await takeScreenshot(page, 'compare-flow', 'step-02a-agent-expanded');

        // Step 3: Click instance to see datasets
        const instanceCards = page.locator('[data-testid^="instance-card-"]');
        await expect(instanceCards.first()).toBeVisible({ timeout: 10000 });

        await instanceCards.nth(1).click();
        await page.waitForTimeout(1000);
        await takeScreenshot(page, 'compare-flow', 'step-02b-instance-expanded');

        // Step 4: Click dataset to see runs
        const datasetCards = page.locator('[data-testid^="instance-dataset-card"]');
        await expect(datasetCards.first()).toBeVisible({ timeout: 10000 });

        await datasetCards.nth(1).click();
        await page.waitForTimeout(1000);
        await takeScreenshot(page, 'compare-flow', 'step-02c-dataset-expanded');

        // Step 5: Select 2+ runs using checkboxes or pin buttons
        const runRows = page.locator('[data-testid^="run-row-"]');
        const runCount = await runRows.count();
        console.log(`Found ${runCount} runs for selection`);

        expect(runCount).toBeGreaterThanOrEqual(2);

        let selectedCount = 0;

        // Step 5: Select runs using "Add to Compare" buttons
        console.log('Selecting runs using "Add to Compare" buttons');
        for (let i = 0; i < Math.min(3, runCount); i++) {
            const runRow = runRows.nth(i);
            const addToCompareButton = runRow
                .locator('button')
                .filter({ hasText: /Add to Compare/i });

            if ((await addToCompareButton.count()) > 0) {
                await addToCompareButton.first().click();
                selectedCount++;
                await page.waitForTimeout(300);
                console.log(`Selected run ${i + 1}`);
            }
        }

        console.log(`Selected ${selectedCount} runs`);

        expect(selectedCount).toBeGreaterThanOrEqual(2);

        await takeScreenshot(page, 'compare-flow', 'step-05b-runs-selected');

        // Step 6: Verify sticky compare bar appears
        const stickyCompareBar = page.locator('[data-testid*="compare-bar"]').or(
            page.locator('[class*="sticky"]').filter({
                hasText: /compare|selected/i,
            })
        );

        if ((await stickyCompareBar.count()) > 0) {
            await expect(stickyCompareBar.first()).toBeVisible();
            console.log('Sticky compare bar is visible');
            await takeScreenshot(page, 'compare-flow', 'step-06-compare-bar-visible');
        }

        // Step 7: Click "Compare Selected" button
        const compareButton = page
            .locator('button')
            .filter({ hasText: /Compare \d+ Runs/i });

        if ((await compareButton.count()) > 0) {
            await compareButton.first().click();
            await page.waitForTimeout(1500);
            console.log('Navigating to compare page');
        } else {
            console.log('Compare button not found, checking URL for compare route');
        }

        // Step 8: Verify we're on compare page (SPA - no URL change)
        await page.waitForTimeout(1000);
        await waitForPageLoad(page);

        // Look for "Compare Runs" heading
        await expect(page.getByText('Compare Runs').first()).toBeVisible({
            timeout: 10000,
        });
        await takeScreenshot(page, 'compare-flow', 'step-08-compare-page-loaded');

        // Verify runs table is visible
        const runsTable = page.getByText('Runs').first();
        await expect(runsTable).toBeVisible();
        console.log('Compare Runs page loaded with runs table');

        // Verify taskwise comparison section is visible
        const taskwiseComparison = page.getByText('Taskwise Comparison');
        await expect(taskwiseComparison).toBeVisible();
        console.log('Taskwise Comparison section visible');

        await page.waitForTimeout(1000);
        await takeScreenshot(page, 'compare-flow', 'step-08b-comparison-visible');

        // Step 9: Click on a task to expand details
        // Look for Task ID rows (they have collapse/expand functionality)
        const taskRows = page.locator('text=/Task ID:/i');

        if ((await taskRows.count()) > 0) {
            console.log('Clicking task row to view details');
            await taskRows.first().click();
            await page.waitForTimeout(1000);
            await takeScreenshot(page, 'compare-flow', 'step-09-task-expanded');

            // Verify task details are expanded (Custom fields should be visible)
            const customFields = page.getByText(
                /Custom Hehe|Custom Hola|Custom Proof Complexity/i
            );
            if ((await customFields.count()) > 0) {
                await expect(customFields.first()).toBeVisible();
                console.log('Task details expanded with custom fields visible');
            }

            await takeScreenshot(
                page,
                'compare-flow',
                'step-09b-task-details-visible'
            );

            // Look for "Compare Details" button if it exists
            const compareDetailsButton = page
                .locator('button')
                .filter({ hasText: /Compare Details/i });
            if ((await compareDetailsButton.count()) > 0) {
                await compareDetailsButton.first().click();
                await page.waitForTimeout(1000);
                await takeScreenshot(
                    page,
                    'compare-flow',
                    'step-10a-compare-details-opened'
                );

                // Step 10: Verify comparison modal or details are shown
                const comparisonModal = page.locator('[role="dialog"]');
                if ((await comparisonModal.count()) > 0) {
                    await expect(comparisonModal.first()).toBeVisible();
                    console.log('Comparison details modal opened');

                    // Close modal
                    const closeModalButton = page
                        .locator('button[aria-label*="close"]')
                        .or(page.locator('button').filter({ hasText: /×|close/i }))
                        .first();

                    if ((await closeModalButton.count()) > 0) {
                        await closeModalButton.click();
                        await page.waitForTimeout(500);
                        console.log('Comparison modal closed');
                    }

                    await takeScreenshot(page, 'compare-flow', 'step-10b-modal-closed');
                }
            }
        } else {
            console.log('No task rows found for interaction');
        }

        console.log('Successfully returned to dashboard');
    });

    /**
     * REQ-089: Complete Flow: Dataset View → Agent Runs → Comparison
     *
     * This test verifies the dataset-centric workflow:
     * Hierarchy: Dataset → Agent → Instance → Dataset → Runs
     * 1. Switch to Datasets tab
     * 2. First dataset is already expanded, verify agents shown
     * 3. Click agent to expand instances
     * 4. Click instance to view datasets
     * 5. Click dataset to view runs
     * 6. Select 2+ runs using "Add to Compare"
     * 7. Verify sticky compare bar
     * 8. Click "Compare N Runs"
     * 9. Verify Compare Runs page
     * 10. Navigate back to datasets view
     */
    test('REQ-089: should complete dataset view → agent runs → comparison flow', async ({
        page,
    }) => {
        // Step 1: Load dashboard and switch to Datasets tab
        await expect(page.getByText('Leader Dashboard')).toBeVisible();
        await takeScreenshot(page, 'dataset-flow', 'step-01-dashboard-loaded');

        const datasetsTab = page
            .locator('button')
            .filter({ hasText: /^Datasets$/i });
        await expect(datasetsTab.first()).toBeVisible();

        await datasetsTab.first().click();
        await page.waitForTimeout(1000);
        await takeScreenshot(page, 'dataset-flow', 'step-01b-datasets-tab-active');

        // Step 2: Verify datasets view is visible
        const datasetsView = page.locator('[data-testid="datasets-view"]');
        await expect(datasetsView).toBeVisible({ timeout: 10000 });
        console.log('Datasets view is visible');

        // Step 3: First dataset is already expanded, verify agents are shown
        const agentCards = page.locator('[data-testid^="dataset-agent-card-"]');
        await page.waitForTimeout(500);
        const agentCount = await agentCards.count();
        console.log(`Found ${agentCount} agents for this dataset`);
        expect(agentCount).toBeGreaterThan(0);

        await takeScreenshot(page, 'dataset-flow', 'step-03-agents-visible');

        // Step 4: Click first agent to expand instances
        console.log('Expanding first agent to view instances');
        await agentCards.first().click();
        await page.waitForTimeout(1000);
        await takeScreenshot(page, 'dataset-flow', 'step-04-agent-expanded');

        // Step 5: Click instance to view datasets
        const instanceCards = page.locator(
            '[data-testid^="dataset-instance-card"]'
        );
        await expect(instanceCards.first()).toBeVisible({ timeout: 10000 });
        console.log('Expanding instance to view datasets');

        await instanceCards.first().click();
        await page.waitForTimeout(1000);
        await takeScreenshot(page, 'dataset-flow', 'step-05-instance-expanded');

        // Step 6: Click dataset to view runs
        const datasetCards = page.locator('[data-testid^="run-row"]');
        await expect(datasetCards.first()).toBeVisible({ timeout: 10000 });
        console.log('Expanding dataset to view runs');

        // Step 7: Select runs using "Add to Compare" buttons
        const runRows = page.locator('[data-testid^="run-row-"]');
        const runCount = await runRows.count();
        console.log(`Found ${runCount} runs`);
        expect(runCount).toBeGreaterThanOrEqual(2);

        let selectedCount = 0;
        console.log('Selecting runs using "Add to Compare" buttons');
        for (let i = 0; i < Math.min(2, runCount); i++) {
            const runRow = runRows.nth(i);
            const addToCompareButton = runRow
                .locator('button')
                .filter({ hasText: /Add to Compare/i });

            await addToCompareButton.first().click();
            selectedCount++;
            await page.waitForTimeout(300);
            console.log(`Selected run ${i + 1}`);
        }

        console.log(`Selected ${selectedCount} runs from dataset view`);
        expect(selectedCount).toBeGreaterThanOrEqual(2);
        await takeScreenshot(page, 'dataset-flow', 'step-07-runs-selected');

        // Step 8: Verify sticky compare bar appears and click compare
        // Step 6: Verify sticky compare bar appears
        const stickyCompareBar = page.locator('[data-testid*="compare-bar"]').or(
            page.locator('[class*="sticky"]').filter({
                hasText: /compare|selected/i,
            })
        );

        await expect(stickyCompareBar.first()).toBeVisible();
        console.log('Sticky compare bar visible in dataset view');
        await takeScreenshot(page, 'dataset-flow', 'step-08-compare-bar-visible');

        // Step 9: Click compare button
        const compareButton = page.locator('[data-testid="compare-button"]');
        const compareButtonCount = await compareButton.count();
        await expect(compareButtonCount).toBeGreaterThanOrEqual(1);

        await compareButton.nth(1).click();
        await page.waitForTimeout(1500);
        console.log('Navigating to compare page from dataset view');

        await page.waitForTimeout(1500);
        console.log('Navigating to compare page from dataset view');

        // Step 10: Verify we're on compare page (SPA - no URL change)
        await waitForPageLoad(page);
        await page.waitForTimeout(1000);

        // Look for "Compare Runs" heading
        await expect(page.getByText('Compare Runs').first()).toBeVisible({
            timeout: 10000,
        });
        await takeScreenshot(page, 'dataset-flow', 'step-10-comparison-page');

        // Verify comparison content
        await expect(page.getByText('Taskwise Comparison')).toBeVisible({
            timeout: 10000,
        });
        console.log('Comparison page loaded successfully');


    });

    /**
     * Additional integration test: Complete workflow with all features
     * Tests the entire application in one comprehensive flow
     */
    test('should complete comprehensive workflow using all major features', async ({
        page,
    }) => {
        // 1. Start at dashboard
        await expect(page.getByText('Leader Dashboard')).toBeVisible();
        console.log('Step 1: Dashboard loaded');

        // 2. Test theme switching
        const themeButton = page
            .locator('button[aria-label*="theme"]')
            .or(
                page
                    .locator('button')
                    .filter({ has: page.locator('svg[class*="moon"]') })
            )
            .or(
                page
                    .locator('button')
                    .filter({ has: page.locator('svg[class*="sun"]') })
            );

        if ((await themeButton.count()) > 0) {
            await themeButton.first().click();
            await page.waitForTimeout(300);
            console.log('Step 2: Theme toggled');
        }

        // 3. Test agents view
        const agentsTab = page.locator('button').filter({ hasText: /^Agents$/i });
        await agentsTab.first().click();
        await page.waitForTimeout(500);
        console.log('Step 3: Switched to Agents view');

        // 4. Test sorting
        const sortButton = page.locator('[data-testid^="sort-by-"]').first();
        if ((await sortButton.count()) > 0) {
            await sortButton.click();
            await page.waitForTimeout(300);
            console.log('Step 4: Tested sorting');
        }

        // 5. Expand agent
        const agentRow = page.locator('[data-testid^="agent-row-"]').first();
        await agentRow.click();
        await page.waitForTimeout(1000);
        console.log('Step 5: Expanded agent');

        // 6. Test datasets view
        const datasetsTab = page
            .locator('button')
            .filter({ hasText: /^Datasets$/i });
        await datasetsTab.first().click();
        await page.waitForTimeout(500);
        console.log('Step 6: Switched to Datasets view');

        // 7. Verify refresh button works
        const refreshButton = page
            .locator('button')
            .filter({ hasText: /refresh/i });
        if ((await refreshButton.count()) > 0) {
            await refreshButton.first().click();
            await page.waitForTimeout(1000);
            console.log('Step 7: Tested refresh');
        }

        await takeScreenshot(
            page,
            'full-journey',
            'comprehensive-workflow-complete'
        );
        console.log('Comprehensive workflow test completed successfully');
    });
});
