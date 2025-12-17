const nextJest = require('next/jest')

const createJestConfig = nextJest({
  // Provide the path to your Next.js app to load next.config.js and .env files
  dir: './',
})

// Add any custom config to be passed to Jest
const customJestConfig = {
  setupFilesAfterEnv: ['<rootDir>/jest.setup.js'],
  testEnvironment: 'jsdom',
  moduleNameMapper: {
    '^@/(.*)$': '<rootDir>/$1',
  },
  testMatch: [
    '**/__tests__/**/*.(ts|tsx|js)',
    '**/*.(test|spec).(ts|tsx|js)',
  ],
  testPathIgnorePatterns: [
    '<rootDir>/tests/',  // Ignore Playwright tests
    '<rootDir>/e2e/',    // Ignore E2E tests
  ],
  collectCoverageFrom: [
    'hooks/**/*.(ts|tsx)',
    'components/**/*.(ts|tsx)',
    'features/**/*.(ts|tsx)',
    '!**/*.d.ts',
  ],
  transformIgnorePatterns: [
    '/node_modules/(?!(react-syntax-highlighter|refractor|hastscript|hast-util-.*|unist-util-.*|property-information|space-separated-tokens|comma-separated-tokens|vfile.*|unified|bail|is-plain-obj|trough|remark-.*|rehype-.*)/)',
  ],
}

// createJestConfig is exported this way to ensure that next/jest can load the Next.js config which is async
module.exports = createJestConfig(customJestConfig)