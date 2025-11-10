import { Page, Route } from '@playwright/test';
import { mockAgentData, mockEmptyData } from '../fixtures';

export class ApiMocker {
  constructor(private page: Page) {}

  async mockAgentsAPI(data = mockAgentData) {
    await this.page.route('**/api/agents**', async (route: Route) => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify(data),
      });
    });
  }

  async mockAgentsAPIError(statusCode = 500, message = 'Internal Server Error') {
    await this.page.route('**/api/agents**', async (route: Route) => {
      await route.fulfill({
        status: statusCode,
        contentType: 'application/json',
        body: JSON.stringify({ error: message }),
      });
    });
  }

  async mockEmptyAgentsAPI() {
    await this.mockAgentsAPI(mockEmptyData);
  }

  async mockSlowAPI(delayMs = 2000) {
    await this.page.route('**/api/agents**', async (route: Route) => {
      await new Promise(resolve => setTimeout(resolve, delayMs));
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify(mockAgentData),
      });
    });
  }

  async mockTaskDetailsAPI(taskId: string, taskData: Record<string, unknown>) {
    await this.page.route(`**/api/tasks/${taskId}**`, async (route: Route) => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify(taskData),
      });
    });
  }

  async clearAllMocks() {
    await this.page.unroute('**/*');
  }
}

// Utility function to set up common mocks
export async function setupDefaultMocks(page: Page) {
  const apiMocker = new ApiMocker(page);
  await apiMocker.mockAgentsAPI();
  return apiMocker;
}