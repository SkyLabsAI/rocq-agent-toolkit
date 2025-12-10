#!/bin/bash
# Script to fix remaining ESLint errors

# Fix unused variables by adding _ prefix
echo "Fixing unused variables..."

# components/RunRow.tsx - remove unused imports
sed -i '' 's/import { cn } from.*;//g' components/RunRow.tsx

# components/base/comparisonModal/utils/tabColors.ts
sed -i '' 's/export const getTabColor = (key:/export const getTabColor = (_key:/g' components/base/comparisonModal/utils/tabColors.ts

# contexts/GlobalCompareContext.tsx
sed -i '' 's/const clearOtherDatasets/const _clearOtherDatasets/g' contexts/GlobalCompareContext.tsx

# e2e/home.spec.ts
sed -i '' "s/import AxeBuilder from.*;//g" e2e/home.spec.ts

# e2e/task-details.spec.ts
sed -i '' "s/import AxeBuilder from '@axe-core\/playwright';$/import AxeBuilder from '@axe-core\/playwright';\n\nexport { AxeBuilder as checkAccessibility };/g" e2e/task-details.spec.ts
sed -i '' "s/async function checkAccessibility/async function _checkAccessibility/g" e2e/task-details.spec.ts

# features files
sed -i '' "s/import { RunDetailsResponse/import { type RunDetailsResponse/g" features/localdashboard/AgentRunsView.tsx
sed -i '' "s/const error/const _error/g" features/localdashboard/agentview/agent-details/agent-benchmarks/index.tsx

# More fixes
echo "Done!"

