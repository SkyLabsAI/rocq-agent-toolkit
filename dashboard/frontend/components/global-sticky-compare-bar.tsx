import { useRouter } from 'next/navigation';
import React from 'react';

import StickyCompareBar from '@/components/sticky-compare-bar';
import { useGlobalCompare } from '@/contexts/global-compare-context';

export const GlobalStickyCompareBar: React.FC = () => {
  const router = useRouter();
  const { selections, clearAllSelections } = useGlobalCompare();

  const hasAgentSelections = selections.selectedAgents.length > 0;
  const hasRunSelections = selections.selectedRuns.length > 0;

  const compareAgents = () => {
    if (selections.selectedAgents.length < 1) return;
    const query = new URLSearchParams({
      agents: selections.selectedAgents.map(a => a.agentName).join(','),
    }).toString();
    router.push(`/compare/agents?${query}`);
  };

  const compareRuns = () => {
    if (selections.selectedRuns.length < 1) return;
    const query = new URLSearchParams({
      runs: selections.selectedRuns.map(r => r.runId).join(','),
    }).toString();
    router.push(`/compare?${query}`);
    router.push(`/compare?${query}`);
  };

  // Show agent comparison bar if agents are selected
  if (hasAgentSelections) {
    return (
      <StickyCompareBar
        selectedItems={selections.selectedAgents.map(a => a.agentName)}
        onCompareSelected={compareAgents}
        onClearSelection={clearAllSelections}
        attribute='Agents'
      />
    );
  }

  // Show run comparison bar if runs are selected
  if (hasRunSelections) {
    return (
      <StickyCompareBar
        selectedItems={selections.selectedRuns.map(r => r.runId)}
        onCompareSelected={compareRuns}
        onClearSelection={clearAllSelections}
        attribute='Runs'
      />
    );
  }

  return null;
};

export default GlobalStickyCompareBar;
