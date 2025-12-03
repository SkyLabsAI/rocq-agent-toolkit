import React from 'react';
import { useNavigate } from 'react-router-dom';
import StickyCompareBar from '@/components/StickyCompareBar';
import { useGlobalCompare } from '@/contexts/GlobalCompareContext';

export const GlobalStickyCompareBar: React.FC = () => {
  const navigate = useNavigate();
  const {
    selections,
    clearAllSelections,
  } = useGlobalCompare();

  const hasAgentSelections = selections.selectedAgents.length > 0;
  const hasRunSelections = selections.selectedRuns.length > 0;

  const compareAgents = () => {
    if (selections.selectedAgents.length < 1) return;
    const query = new URLSearchParams({
      agents: selections.selectedAgents.map(a => a.agentName).join(','),
    }).toString();
    navigate({
      pathname: '/compare/agents',
      search: `?${query}`,
    });
  };

  const compareRuns = () => {
    if (selections.selectedRuns.length < 1) return;
    const query = new URLSearchParams({
      runs: selections.selectedRuns.map(r => r.runId).join(','),
    }).toString();
    navigate({
      pathname: '/compare',
      search: `?${query}`,
    });
  };

  // Show agent comparison bar if agents are selected
  if (hasAgentSelections) {
    return (
      <StickyCompareBar
        selectedItems={selections.selectedAgents.map(a => a.agentName)}
        onCompareSelected={compareAgents}
        onClearSelection={clearAllSelections}
        attribute="Agents"
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
        attribute="Runs"
      />
    );
  }

  return null;
};