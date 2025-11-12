import { defineConfig, devices } from '@playwright/test';

export default defineConfig({
  testDir: 'tests',
  timeout: 30000,
  expect: {
    timeout: 5000,
    // Visual comparisons
    toHaveScreenshot: { threshold: 0.2, animations: 'disabled' },
    toMatchSnapshot: { threshold: 0.2 }
  },
  fullyParallel: true,
  forbidOnly: !!process.env.CI,
  retries: process.env.CI ? 2 : 0,
  workers: process.env.CI ? 1 : undefined,
  
  reporter: [
    ['html', { open: 'never' }],
    ['list'],
    ['json', { outputFile: 'test-results/results.json' }],
    ['junit', { outputFile: 'test-results/junit.xml' }]
  ],
  
  use: {
    baseURL: 'http://localhost:3000',
    trace: 'on',
    screenshot: 'on',
    video: 'on',
    // Collect performance metrics
    extraHTTPHeaders: {
      'Accept-Language': 'en-US,en;q=0.9',
    },
  },
  
  webServer: {
    command: 'NEXT_PUBLIC_USE_MOCK_DATA=false pnpm dev',
    port: 3000,
    reuseExistingServer: true, // Always reuse existing server
    timeout: 120 * 1000, // 2 minutes
    stdout: 'pipe', // Capture server output for debugging
    stderr: 'pipe',
    env: {
      NEXT_PUBLIC_USE_MOCK_DATA: 'false',
    },
  },
  
  projects: [
    // Desktop browsers
    {
      name: 'chromium',
      use: { ...devices['Desktop Chrome'] },
    },
    {
      name: 'firefox',
      use: { ...devices['Desktop Firefox'] },
    },
    {
      name: 'webkit',
      use: { ...devices['Desktop Safari'] },
    },
    
    // Mobile browsers
    {
      name: 'mobile-chrome',
      use: { ...devices['Pixel 5'] },
    },
    {
      name: 'mobile-safari',
      use: { ...devices['iPhone 12'] },
    },
    
    // Accessibility testing
    {
      name: 'chromium-accessibility',
      use: { 
        ...devices['Desktop Chrome'],
        // Force reduced motion for consistent screenshots
        extraHTTPHeaders: {
          'Sec-CH-Prefers-Reduced-Motion': 'reduce'
        }
      },
      testMatch: '**/*.a11y.spec.ts'
    }
  ],
});