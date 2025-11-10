import { Page, Locator, expect } from '@playwright/test';

export class TaskDetailsModal {
  readonly page: Page;
  readonly modal: Locator;
  readonly closeButton: Locator;
  readonly modalTitle: Locator;
  readonly tabButtons: Locator;
  readonly tabContent: Locator;
  readonly codeViewer: Locator;
  readonly jsonViewer: Locator;

  constructor(page: Page) {
    this.page = page;
    this.modal = page.getByRole('dialog');
    this.closeButton = page.getByRole('button', { name: /close/i });
    this.modalTitle = this.modal.locator('h2').first();
    this.tabButtons = this.modal.locator('[role="tab"]');
    this.tabContent = this.modal.locator('[role="tabpanel"]');
    this.codeViewer = this.modal.getByTestId('code-viewer');
    this.jsonViewer = this.modal.getByTestId('json-viewer');
  }

  async waitForOpen() {
    await expect(this.modal).toBeVisible();
  }

  async close() {
    await this.closeButton.click();
    await expect(this.modal).toBeHidden();
  }

  async closeByEscape() {
    await this.page.keyboard.press('Escape');
    await expect(this.modal).toBeHidden();
  }

  async closeByBackdrop() {
    // Click outside the modal content
    await this.page.locator('.modal-backdrop').click({ position: { x: 10, y: 10 } });
    await expect(this.modal).toBeHidden();
  }

  async verifyTitle(expectedTitle: string) {
    await expect(this.modalTitle).toContainText(expectedTitle);
  }

  async getAvailableTabs(): Promise<string[]> {
    const tabs = await this.tabButtons.allTextContents();
    return tabs.filter(Boolean);
  }

  async switchToTab(tabName: string) {
    const tab = this.page.getByRole('tab', { name: new RegExp(tabName, 'i') });
    await expect(tab).toBeVisible();
    await tab.click();
    
    // Wait for tab content to load
    await this.page.waitForTimeout(100);
  }

  async verifyTabContent(tabName: string, expectedContent?: string) {
    await this.switchToTab(tabName);
    
    const activeTabContent = this.tabContent.filter({ hasText: expectedContent || '' });
    await expect(activeTabContent).toBeVisible();
    
    if (expectedContent) {
      await expect(activeTabContent).toContainText(expectedContent);
    }
  }

  async verifyCodeViewerContent(expectedCode: string) {
    await expect(this.codeViewer).toBeVisible();
    await expect(this.codeViewer).toContainText(expectedCode);
  }

  async verifyJsonContent(key: string, expectedValue: string) {
    const jsonContent = this.jsonViewer.locator(`text="${key}"`);
    await expect(jsonContent).toBeVisible();
    
    const valueContent = this.jsonViewer.locator(`text="${expectedValue}"`);
    await expect(valueContent).toBeVisible();
  }

  async verifyModalAccessibility() {
    // Check ARIA attributes
    await expect(this.modal).toHaveAttribute('role', 'dialog');
    await expect(this.modal).toHaveAttribute('aria-modal', 'true');
    
    // Check focus management
    const focusedElement = this.page.locator(':focus');
    await expect(focusedElement).toBeVisible();
  }

  async verifyTabKeyNavigation() {
    // Test keyboard navigation through tabs
    const tabs = await this.getAvailableTabs();
    
    for (let i = 0; i < tabs.length; i++) {
      await this.page.keyboard.press('Tab');
      const focusedTab = this.page.locator(':focus');
      await expect(focusedTab).toHaveAttribute('role', 'tab');
    }
  }
}