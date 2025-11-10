import { test as base, expect, Page } from '@playwright/test';
import { HomePage } from '../pages/HomePage';
import { TaskDetailsModal } from '../pages/TaskDetailsModal';

// Mock data fixtures
export const mockAgentData = {
  agents: [
    {
      id: 'agent-1',
      name: 'Test Agent 1',
      status: 'active',
      performance: 85.5,
      totalRuns: 42,
      successRate: 0.85,
      lastRun: '2025-11-10T10:00:00Z',
      tasks: [
        {
          id: 'task-1',
          name: 'Test Task 1',
          status: 'completed',
          duration: 1500,
          cpp_code: 'int main() { return 0; }',
          logs: ['Starting task...', 'Task completed successfully']
        },
        {
          id: 'task-2',
          name: 'Test Task 2', 
          status: 'failed',
          duration: 2300,
          cpp_code: 'int factorial(int n) { return n <= 1 ? 1 : n * factorial(n-1); }',
          logs: ['Starting task...', 'Error occurred', 'Task failed']
        }
      ]
    },
    {
      id: 'agent-2',
      name: 'Test Agent 2',
      status: 'idle',
      performance: 92.1,
      totalRuns: 68,
      successRate: 0.92,
      lastRun: '2025-11-10T09:30:00Z',
      tasks: []
    }
  ]
};

export const mockEmptyData = {
  agents: []
};

// Extended test with fixtures
type TestFixtures = {
  homePage: HomePage;
  taskModal: TaskDetailsModal;
};

export const test = base.extend<TestFixtures>({
  homePage: async ({ page }, use) => {
    const homePage = new HomePage(page);
    await use(homePage);
  },
  
  taskModal: async ({ page }, use) => {
    const taskModal = new TaskDetailsModal(page);
    await use(taskModal);
  }
});

export { expect };