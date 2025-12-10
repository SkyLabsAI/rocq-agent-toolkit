import { test as base } from '@playwright/test';

/**
 * Custom fixtures for tests
 * Currently extends the base Playwright test without additional customizations
 * Can be extended in the future with app-specific fixtures
 */
export const test = base;

export { expect } from '@playwright/test';
