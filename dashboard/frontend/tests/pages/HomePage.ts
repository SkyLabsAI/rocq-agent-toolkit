import { Page, Locator, expect } from '@playwright/test';

export class HomePage {
  readonly page: Page;
  readonly dashboardTitle: Locator;
  readonly agentTable: Locator;
  readonly refreshButton: Locator;
  readonly loadingSpinner: Locator;
  readonly errorMessage: Locator;
  readonly agentRows: Locator;

  constructor(page: Page) {
    this.page = page;
    this.dashboardTitle = page.getByRole('heading', { name: /Agent Performance/i });
    this.agentTable = page.getByRole('table');
    this.refreshButton = page.getByRole('button', { name: /refresh data/i });
    this.loadingSpinner = page.getByTestId('loading-spinner');
    this.errorMessage = page.getByTestId('error-message');
    this.agentRows = page.locator('tbody tr');
  }

  async goto() {
    await this.page.goto('/');
    await this.waitForPageLoad();
  }

  async waitForPageLoad() {
    // Wait for either the table to load or error message to appear
    await Promise.race([
      this.agentTable.waitFor({ state: 'visible' }),
      this.errorMessage.waitFor({ state: 'visible' })
    ]);
  }

  async refreshData() {
    await this.refreshButton.click();
    await this.waitForPageLoad();
  }

  async getAgentRowCount(): Promise<number> {
    return await this.agentRows.count();
  }

  async expandAgentRow(index: number = 0) {
    const row = this.agentRows.nth(index);
    await expect(row).toBeVisible();
    await row.click();
    // Wait for expansion animation
    await this.page.waitForTimeout(300);
  }

  async getAgentRowByName(name: string): Promise<Locator> {
    return this.page.locator(`tr:has-text("${name}")`);
  }

  async openTaskModal(agentIndex: number = 0, taskIndex: number = 0) {
    await this.expandAgentRow(agentIndex);
    
    const viewLogsButton = this.page
      .getByRole('button', { name: /view logs/i })
      .nth(taskIndex);
      
    await expect(viewLogsButton).toBeVisible();
    await viewLogsButton.click();
  }

  async verifyDashboardLoaded() {
    await expect(this.dashboardTitle).toBeVisible();
    await expect(this.agentTable).toBeVisible();
    await expect(this.refreshButton).toBeVisible();
    await expect(this.refreshButton).toBeEnabled();
  }

  async verifyEmptyState() {
    await expect(this.agentTable).toBeVisible();
    const rowCount = await this.getAgentRowCount();
    expect(rowCount).toBe(0);
  }

  async verifyAgentData(expectedCount: number) {
    const rowCount = await this.getAgentRowCount();
    expect(rowCount).toBe(expectedCount);
  }
}