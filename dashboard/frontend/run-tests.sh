#!/bin/bash

# Playwright Test Runner Script
# Usage: ./run-tests.sh [test-type] [browser]

set -e

TEST_TYPE=${1:-"all"}
BROWSER=${2:-"chromium"}

echo "🎭 Playwright Test Runner"
echo "=========================="

# Function to check if server is running
check_server() {
  if curl -s http://localhost:3000 > /dev/null 2>&1; then
    echo "✅ Development server is already running on http://localhost:3000"
    return 0
  else
    echo "❌ No development server found on http://localhost:3000"
    return 1
  fi
}

# Function to start server if needed  
start_server_if_needed() {
  if ! check_server; then
    echo "🚀 Starting development server..."
    pnpm dev &
    SERVER_PID=$!
    
    # Wait for server to be ready
    echo "⏳ Waiting for server to be ready..."
    for i in {1..30}; do
      if curl -s http://localhost:3000 > /dev/null 2>&1; then
        echo "✅ Server is ready!"
        break
      fi
      sleep 2
    done
    
    if ! curl -s http://localhost:3000 > /dev/null 2>&1; then
      echo "❌ Failed to start server"
      exit 1
    fi
  fi
}

# Function to run tests based on type
run_tests() {
  case $TEST_TYPE in
    "all")
      echo "🧪 Running all tests with browser: $BROWSER"
      npx playwright test --project=$BROWSER
      ;;
    "dashboard")
      echo "🏠 Running dashboard tests"
      npx playwright test tests/dashboard/ --project=$BROWSER
      ;;
    "modal")
      echo "🔲 Running modal tests"
      npx playwright test tests/taskModal/ --project=$BROWSER
      ;;
    "integration")
      echo "🔗 Running integration tests"
      npx playwright test tests/integration/ --project=$BROWSER
      ;;
    "accessibility"|"a11y")
      echo "♿ Running accessibility tests"
      npx playwright test tests/accessibility/ --project=chromium
      ;;
    "ui")
      echo "🖥️ Running tests in UI mode"
      npx playwright test --ui
      ;;
    "debug")
      echo "🐛 Running tests in debug mode"
      npx playwright test --debug
      ;;
    *)
      echo "❌ Unknown test type: $TEST_TYPE"
      echo "Available types: all, dashboard, modal, integration, accessibility, ui, debug"
      exit 1
      ;;
  esac
}

# Function to show report
show_report() {
  echo ""
  echo "📊 Opening test report..."
  npx playwright show-report
}

# Main execution
echo "📋 Test configuration:"
echo "  - Test type: $TEST_TYPE"  
echo "  - Browser: $BROWSER"
echo ""

# Check if we're in the right directory
if [ ! -f "playwright.config.ts" ]; then
  echo "❌ playwright.config.ts not found. Make sure you're in the frontend directory."
  exit 1
fi

# Start server if needed (only for local runs)
if [ "$CI" != "true" ]; then
  start_server_if_needed
fi

# Install dependencies if needed
if [ ! -d "node_modules/@playwright" ]; then
  echo "📦 Installing Playwright..."
  npx playwright install --with-deps
fi

# Run the tests
run_tests

# Show results
echo ""
echo "✅ Tests completed!"
echo ""
echo "🎯 Available commands:"
echo "  - View report: npx playwright show-report"
echo "  - Run specific test: npx playwright test [test-file]"
echo "  - Run with UI: npx playwright test --ui"
echo "  - Debug mode: npx playwright test --debug"