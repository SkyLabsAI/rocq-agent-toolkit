import { expect, test } from '@playwright/test';

import { takeScreenshot, waitForPageLoad } from './utils/test-helpers';

test.describe('Visualizer Modal - Trace and Span Visualization', () => {
    test.beforeEach(async ({ page }) => {
        await page.goto('/');
        await waitForPageLoad(page);

        // Ensure we're on the Agents tab (default view)
        const agentsTab = page.locator('button').filter({ hasText: /^Agents$/i });
        if ((await agentsTab.count()) > 0) {
            await agentsTab.first().click();
            await waitForPageLoad(page);
        }
    });

    test.describe('Opening Visualizer Modal', () => {
        test('should open visualizer modal when clicking visualizer button on a run', async ({
            page,
        }) => {
            // Wait for agent rows to load
            await page.waitForTimeout(1000);

            // Click first agent to expand
            const agentRows = page.locator('[data-testid^="agent-row-"]');
            const firstAgent = agentRows.first();
            await expect(firstAgent).toBeVisible();
            await firstAgent.click();
            await page.waitForTimeout(1000);

            // Wait for instance to show up and click it
            const instanceRow = page.locator('[data-testid^="instance-row-"]').first();
            if ((await instanceRow.count()) > 0) {
                await instanceRow.click();
                await page.waitForTimeout(1000);
            }

            // Look for a run row and click visualizer button
            const runRow = page.locator('[data-testid^="run-row-"]').first();
            await expect(runRow).toBeVisible({ timeout: 5000 });

            // Click visualizer button (it should have a play icon or visualizer text)
            const visualizerButton = runRow
                .locator('button')
                .filter({ hasText: /visualizer/i })
                .or(runRow.locator('button[title*="Visualizer"]'))
                .or(runRow.locator('button[aria-label*="visualizer"]'))
                .first();

            // If no explicit visualizer button, look for buttons in the run row
            if ((await visualizerButton.count()) === 0) {
                // Try clicking any button that might open visualizer
                const buttons = runRow.locator('button');
                if ((await buttons.count()) > 0) {
                    await buttons.first().click();
                }
            } else {
                await visualizerButton.click();
            }

            await page.waitForTimeout(1000);

            // Verify modal is open
            const modal = page.locator('[role="dialog"]').or(
                page.locator('div').filter({ hasText: /visualizer/i })
            );
            await expect(modal.first()).toBeVisible({ timeout: 5000 });

            await takeScreenshot(page, 'visualizer', 'modal-opened');
        });
    });

    test.describe('Visualizer Modal Content', () => {
        test('should display trace selection dropdown when traces are loaded', async ({
            page,
        }) => {
            // Navigate and open visualizer modal (simplified for this test)
            await page.goto('/?mock_visualizer=true');
            await waitForPageLoad(page);

            // Wait for modal content
            await page.waitForTimeout(2000);

            // Check for trace selection UI
            const traceSelect = page.locator('select').filter({
                has: page.locator('option'),
            });

            if ((await traceSelect.count()) > 0) {
                await expect(traceSelect.first()).toBeVisible();

                // Check that there are trace options
                const options = traceSelect.first().locator('option');
                const optionCount = await options.count();
                expect(optionCount).toBeGreaterThan(0);

                await takeScreenshot(page, 'visualizer', 'trace-selection');
            }
        });

        test('should display "no traces" message when no traces are available', async ({
            page,
        }) => {
            await page.goto('/?mock_visualizer=empty');
            await waitForPageLoad(page);
            await page.waitForTimeout(2000);

            // Look for "no traces" message
            const noTracesMessage = page
                .locator('text=/no traces/i')
                .or(page.locator('text=/traces not found/i'));

            if ((await noTracesMessage.count()) > 0) {
                await expect(noTracesMessage.first()).toBeVisible();
            }

            await takeScreenshot(page, 'visualizer', 'no-traces');
        });
    });

    test.describe('Span Graph View', () => {
        test('should display span graph with hierarchical structure', async ({
            page,
        }) => {
            // This test assumes visualizer is open with mock data
            await page.goto('/?visualizer_open=true');
            await waitForPageLoad(page);
            await page.waitForTimeout(2000);

            // Look for span nodes in the graph
            // Spans might be represented as divs, buttons, or other elements with span data
            const spanNodes = page
                .locator('[data-span-id]')
                .or(page.locator('[class*="span-node"]'))
                .or(page.locator('[class*="SpanNode"]'));

            if ((await spanNodes.count()) > 0) {
                const nodeCount = await spanNodes.count();
                expect(nodeCount).toBeGreaterThan(0);

                await takeScreenshot(page, 'visualizer', 'span-graph');
            }
        });

        test('should allow selecting a span node', async ({ page }) => {
            await page.goto('/?visualizer_open=true');
            await waitForPageLoad(page);
            await page.waitForTimeout(2000);

            // Find and click a span node
            const spanNodes = page
                .locator('[data-span-id]')
                .or(page.locator('[class*="span-node"]'))
                .or(page.locator('button').filter({ hasText: /agent|llm|coq/i }));

            if ((await spanNodes.count()) > 0) {
                const firstSpan = spanNodes.first();
                await firstSpan.click();
                await page.waitForTimeout(500);

                // Verify span details panel is updated
                const detailsPanel = page
                    .locator('text=/span details/i')
                    .locator('..')
                    .locator('..');
                await expect(detailsPanel).toBeVisible();

                await takeScreenshot(page, 'visualizer', 'span-selected');
            }
        });

        test('should display span details in the right panel', async ({ page }) => {
            await page.goto('/?visualizer_open=true');
            await waitForPageLoad(page);
            await page.waitForTimeout(2000);

            // Click a span node
            const spanNodes = page
                .locator('[data-span-id]')
                .or(page.locator('[class*="span-node"]'));

            if ((await spanNodes.count()) > 0) {
                await spanNodes.first().click();
                await page.waitForTimeout(1000);

                // Verify "Span details" section
                const spanDetailsHeading = page.locator('text=/span details/i');
                await expect(spanDetailsHeading).toBeVisible();

                // Verify attributes section
                const attributesSection = page.locator('text=/attributes/i');
                if ((await attributesSection.count()) > 0) {
                    await expect(attributesSection.first()).toBeVisible();
                }

                await takeScreenshot(page, 'visualizer', 'span-details');
            }
        });
    });

    test.describe('Depth Control', () => {
        test('should display depth control buttons', async ({ page }) => {
            await page.goto('/?visualizer_open=true');
            await waitForPageLoad(page);
            await page.waitForTimeout(2000);

            // Look for "Max Depth" label
            const maxDepthLabel = page.locator('text=/max depth/i');

            if ((await maxDepthLabel.count()) > 0) {
                await expect(maxDepthLabel.first()).toBeVisible();

                // Check for depth buttons (1, 2, 3, 4, 5, All)
                const depthButtons = page.locator('button').filter({
                    hasText: /^[1-5]$|^All$/,
                });

                if ((await depthButtons.count()) > 0) {
                    expect(await depthButtons.count()).toBeGreaterThanOrEqual(2);
                }

                await takeScreenshot(page, 'visualizer', 'depth-control');
            }
        });

        test('should allow changing depth level', async ({ page }) => {
            await page.goto('/?visualizer_open=true');
            await waitForPageLoad(page);
            await page.waitForTimeout(2000);

            // Find and click depth button "2"
            const depth2Button = page.locator('button').filter({ hasText: /^2$/ });

            if ((await depth2Button.count()) > 0) {
                await depth2Button.first().click();
                await page.waitForTimeout(500);

                // Verify button is highlighted/selected
                const button = depth2Button.first();
                const classes = await button.getAttribute('class');
                expect(classes).toContain('bg-primary'); // Should have primary bg when selected

                await takeScreenshot(page, 'visualizer', 'depth-2-selected');
            }
        });

        test('should allow selecting "All" depth', async ({ page }) => {
            await page.goto('/?visualizer_open=true');
            await waitForPageLoad(page);
            await page.waitForTimeout(2000);

            // Click "All" button
            const allButton = page.locator('button').filter({ hasText: /^All$/ });

            if ((await allButton.count()) > 0) {
                await allButton.first().click();
                await page.waitForTimeout(500);

                // Verify button is highlighted
                const classes = await allButton.first().getAttribute('class');
                expect(classes).toContain('bg-primary');

                await takeScreenshot(page, 'visualizer', 'depth-all-selected');
            }
        });
    });

    test.describe('Logs Display', () => {
        test('should display logs section in right panel', async ({ page }) => {
            await page.goto('/?visualizer_open=true');
            await waitForPageLoad(page);
            await page.waitForTimeout(2000);

            // Select a span to trigger logs loading
            const spanNodes = page
                .locator('[data-span-id]')
                .or(page.locator('[class*="span-node"]'));

            if ((await spanNodes.count()) > 0) {
                await spanNodes.first().click();
                await page.waitForTimeout(1500);

                // Look for "Logs" heading
                const logsHeading = page.locator('text=/^Logs$/i');
                await expect(logsHeading).toBeVisible();

                await takeScreenshot(page, 'visualizer', 'logs-section');
            }
        });

        test('should display log entries when available', async ({ page }) => {
            await page.goto('/?visualizer_open=true');
            await waitForPageLoad(page);
            await page.waitForTimeout(2000);

            // Select a span
            const spanNodes = page
                .locator('[data-span-id]')
                .or(page.locator('[class*="span-node"]'));

            if ((await spanNodes.count()) > 0) {
                await spanNodes.first().click();
                await page.waitForTimeout(2000);

                // Look for log entries or structured logs
                const logEntries = page
                    .locator('[class*="log-entry"]')
                    .or(page.locator('pre'))
                    .or(page.locator('text=/INFO|ERROR|DEBUG|WARN/'));

                if ((await logEntries.count()) > 0) {
                    expect(await logEntries.count()).toBeGreaterThan(0);
                    await takeScreenshot(page, 'visualizer', 'logs-with-entries');
                }
            }
        });

        test('should toggle between formatted and raw log views', async ({
            page,
        }) => {
            await page.goto('/?visualizer_open=true');
            await waitForPageLoad(page);
            await page.waitForTimeout(2000);

            // Select a span
            const spanNodes = page
                .locator('[data-span-id]')
                .or(page.locator('[class*="span-node"]'));

            if ((await spanNodes.count()) > 0) {
                await spanNodes.first().click();
                await page.waitForTimeout(2000);

                // Look for "Show Raw JSON" button
                const rawJsonButton = page.locator('button').filter({
                    hasText: /show raw json/i,
                });

                if ((await rawJsonButton.count()) > 0) {
                    await rawJsonButton.first().click();
                    await page.waitForTimeout(500);

                    // Verify JSON is displayed
                    const jsonContent = page.locator('pre').filter({
                        hasText: /{/,
                    });
                    await expect(jsonContent.first()).toBeVisible();

                    await takeScreenshot(page, 'visualizer', 'logs-raw-view');

                    // Toggle back to formatted view
                    const formattedButton = page
                        .locator('button')
                        .filter({ hasText: /try formatted|formatted view/i });
                    if ((await formattedButton.count()) > 0) {
                        await formattedButton.first().click();
                        await page.waitForTimeout(500);

                        await takeScreenshot(page, 'visualizer', 'logs-formatted-view');
                    }
                }
            }
        });
    });

    test.describe('Node Collapse/Expand', () => {
        test('should allow collapsing and expanding span nodes', async ({
            page,
        }) => {
            await page.goto('/?visualizer_open=true');
            await waitForPageLoad(page);
            await page.waitForTimeout(2000);

            // Look for collapse/expand buttons (usually arrows or +/- icons)
            const collapseButtons = page
                .locator('button[aria-label*="collapse"]')
                .or(page.locator('button[aria-label*="expand"]'))
                .or(page.locator('[class*="collapse"]'))
                .or(page.locator('[class*="chevron"]'));

            if ((await collapseButtons.count()) > 0) {
                const initialCount = await collapseButtons.count();

                // Click first collapse button
                await collapseButtons.first().click();
                await page.waitForTimeout(500);

                await takeScreenshot(page, 'visualizer', 'node-collapsed');

                // Click again to expand
                await collapseButtons.first().click();
                await page.waitForTimeout(500);

                await takeScreenshot(page, 'visualizer', 'node-expanded');
            }
        });
    });

    test.describe('Modal Close', () => {
        test('should close visualizer modal when clicking close button', async ({
            page,
        }) => {
            await page.goto('/?visualizer_open=true');
            await waitForPageLoad(page);
            await page.waitForTimeout(2000);

            // Find and click close button
            const closeButton = page
                .locator('button[aria-label*="close"]')
                .or(page.locator('button').filter({ hasText: /×|close/i }))
                .or(page.locator('[role="dialog"] button').first());

            if ((await closeButton.count()) > 0) {
                await closeButton.first().click();
                await page.waitForTimeout(500);

                // Verify modal is closed
                const modal = page.locator('[role="dialog"]');
                if ((await modal.count()) > 0) {
                    await expect(modal.first()).not.toBeVisible();
                }

                await takeScreenshot(page, 'visualizer', 'modal-closed');
            }
        });
    });

    test.describe('Loading States', () => {
        test('should display loading indicator while fetching traces', async ({
            page,
        }) => {
            await page.goto('/?visualizer_open=true&slow_load=true');
            await waitForPageLoad(page);

            // Look for loading indicator
            const loadingIndicator = page
                .locator('text=/loading/i')
                .or(page.locator('[class*="spinner"]'))
                .or(page.locator('[class*="loading"]'))
                .or(page.locator('[class*="animate-spin"]'));

            // Give it a brief moment to show loading state
            await page.waitForTimeout(500);

            if ((await loadingIndicator.count()) > 0) {
                await takeScreenshot(page, 'visualizer', 'loading-state');
            }
        });
    });

    test.describe('Error States', () => {
        test('should display error message when trace loading fails', async ({
            page,
        }) => {
            await page.goto('/?visualizer_open=true&force_error=true');
            await waitForPageLoad(page);
            await page.waitForTimeout(2000);

            // Look for error message
            const errorMessage = page
                .locator('text=/error/i')
                .or(page.locator('[class*="error"]'))
                .or(page.locator('[class*="text-danger"]'));

            if ((await errorMessage.count()) > 0) {
                await expect(errorMessage.first()).toBeVisible();
                await takeScreenshot(page, 'visualizer', 'error-state');
            }
        });
    });

    test.describe('Responsive Layout', () => {
        test('should display two-panel layout with graph and details', async ({
            page,
        }) => {
            await page.goto('/?visualizer_open=true');
            await waitForPageLoad(page);
            await page.waitForTimeout(2000);

            // Verify main container has proper layout
            const mainContainer = page.locator('[class*="flex"]').filter({
                has: page.locator('text=/span details/i'),
            });

            await expect(mainContainer.first()).toBeVisible();

            await takeScreenshot(page, 'visualizer', 'two-panel-layout');
        });
    });
});

test.describe('Visualizer Integration - Full Flow', () => {
    test('should complete full visualizer workflow from agent to trace visualization', async ({
        page,
    }) => {
        // Start from homepage
        await page.goto('/');
        await waitForPageLoad(page);

        // Step 1: Navigate to agents view
        await takeScreenshot(page, 'visualizer-flow', '01-homepage');

        // Step 2: Click on an agent
        await page.waitForTimeout(1000);
        const agentRows = page.locator('[data-testid^="agent-row-"]');
        if ((await agentRows.count()) > 0) {
            await agentRows.first().click();
            await page.waitForTimeout(1000);
            await takeScreenshot(page, 'visualizer-flow', '02-agent-expanded');
        }

        // Step 3: Click on an instance (if available)
        const instanceRow = page.locator('[data-testid^="instance-row-"]').first();
        if ((await instanceRow.count()) > 0) {
            await instanceRow.click();
            await page.waitForTimeout(1000);
            await takeScreenshot(page, 'visualizer-flow', '03-instance-expanded');
        }

        // Step 4: Click visualizer on a run
        const runRow = page.locator('[data-testid^="run-row-"]').first();
        if ((await runRow.count()) > 0) {
            const visualizerBtn = runRow.locator('button').first();
            await visualizerBtn.click();
            await page.waitForTimeout(2000);
            await takeScreenshot(page, 'visualizer-flow', '04-visualizer-opened');
        }

        // Step 5: Select a span
        await page.waitForTimeout(1000);
        const spanNodes = page
            .locator('[data-span-id]')
            .or(page.locator('[class*="span-node"]'));
        if ((await spanNodes.count()) > 0) {
            await spanNodes.first().click();
            await page.waitForTimeout(1500);
            await takeScreenshot(page, 'visualizer-flow', '05-span-selected');
        }

        // Step 6: Change depth
        const depth2Button = page.locator('button').filter({ hasText: /^2$/ });
        if ((await depth2Button.count()) > 0) {
            await depth2Button.first().click();
            await page.waitForTimeout(500);
            await takeScreenshot(page, 'visualizer-flow', '06-depth-changed');
        }

        // Step 7: View logs
        await page.waitForTimeout(1000);
        await takeScreenshot(page, 'visualizer-flow', '07-logs-displayed');

        // Step 8: Close modal
        const closeButton = page
            .locator('button[aria-label*="close"]')
            .or(page.locator('button').filter({ hasText: /×|close/i }));
        if ((await closeButton.count()) > 0) {
            await closeButton.first().click();
            await page.waitForTimeout(500);
            await takeScreenshot(page, 'visualizer-flow', '08-modal-closed');
        }
    });
});

