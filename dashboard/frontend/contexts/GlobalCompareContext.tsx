import React, {
  createContext,
  useContext,
  useState,
  useCallback,
  ReactNode,
} from 'react';

export interface GlobalSelection {
  selectedAgents: Array<{ agentName: string; datasetId: string }>;
  selectedRuns: Array<{ runId: string; datasetId: string }>;
  activeDatasetId: string | null;
}

interface GlobalCompareContextProps {
  selections: GlobalSelection;
  selectAgent: (agentName: string, datasetId: string) => void;
  deselectAgent: (agentName: string, datasetId: string) => void;
  selectRun: (runId: string, datasetId: string) => void;
  deselectRun: (runId: string, datasetId: string) => void;
  clearAllSelections: () => void;
  clearDatasetSelections: (datasetId: string) => void;
  getSelectedAgentsForDataset: (datasetId: string) => string[];
  getSelectedRunsForDataset: (datasetId: string) => string[];
  isAgentSelected: (agentName: string, datasetId: string) => boolean;
  isRunSelected: (runId: string, datasetId: string) => boolean;
}

const GlobalCompareContext = createContext<
  GlobalCompareContextProps | undefined
>(undefined);

export const useGlobalCompare = () => {
  const context = useContext(GlobalCompareContext);
  if (!context) {
    throw new Error(
      'useGlobalCompare must be used within GlobalCompareProvider'
    );
  }
  return context;
};

interface GlobalCompareProviderProps {
  children: ReactNode;
}

export const GlobalCompareProvider: React.FC<GlobalCompareProviderProps> = ({
  children,
}) => {
  const [selections, setSelections] = useState<GlobalSelection>({
    selectedAgents: [],
    selectedRuns: [],
    activeDatasetId: null,
  });

  const clearOtherDatasets = useCallback((currentDatasetId: string) => {
    setSelections(prev => ({
      ...prev,
      selectedAgents: prev.selectedAgents.filter(
        a => a.datasetId === currentDatasetId
      ),
      selectedRuns: prev.selectedRuns.filter(
        r => r.datasetId === currentDatasetId
      ),
      activeDatasetId: currentDatasetId,
    }));
  }, []);

  const selectAgent = useCallback((agentName: string, datasetId: string) => {
    setSelections(prev => {
      // If switching to a different dataset, clear other selections
      if (prev.activeDatasetId !== null && prev.activeDatasetId !== datasetId) {
        return {
          selectedAgents: [{ agentName, datasetId }],
          selectedRuns: [],
          activeDatasetId: datasetId,
        };
      }

      // Add agent if not already selected
      if (
        !prev.selectedAgents.some(
          a => a.agentName === agentName && a.datasetId === datasetId
        )
      ) {
        return {
          ...prev,
          selectedAgents: [...prev.selectedAgents, { agentName, datasetId }],
          activeDatasetId: datasetId,
        };
      }
      return prev;
    });
  }, []);

  const deselectAgent = useCallback((agentName: string, datasetId: string) => {
    setSelections(prev => ({
      ...prev,
      selectedAgents: prev.selectedAgents.filter(
        a => !(a.agentName === agentName && a.datasetId === datasetId)
      ),
      activeDatasetId:
        prev.selectedAgents.length <= 1 ? null : prev.activeDatasetId,
    }));
  }, []);

  const selectRun = useCallback((runId: string, datasetId: string) => {
    setSelections(prev => {
      // If switching to a different dataset, clear other selections
      if (prev.activeDatasetId !== null && prev.activeDatasetId !== datasetId) {
        return {
          selectedAgents: [],
          selectedRuns: [{ runId, datasetId }],
          activeDatasetId: datasetId,
        };
      }

      // Add run if not already selected
      if (
        !prev.selectedRuns.some(
          r => r.runId === runId && r.datasetId === datasetId
        )
      ) {
        return {
          ...prev,
          selectedRuns: [...prev.selectedRuns, { runId, datasetId }],
          activeDatasetId: datasetId,
        };
      }
      return prev;
    });
  }, []);

  const deselectRun = useCallback((runId: string, datasetId: string) => {
    setSelections(prev => ({
      ...prev,
      selectedRuns: prev.selectedRuns.filter(
        r => !(r.runId === runId && r.datasetId === datasetId)
      ),
      activeDatasetId:
        prev.selectedRuns.length <= 1 ? null : prev.activeDatasetId,
    }));
  }, []);

  const clearAllSelections = useCallback(() => {
    setSelections({
      selectedAgents: [],
      selectedRuns: [],
      activeDatasetId: null,
    });
  }, []);

  const clearDatasetSelections = useCallback((datasetId: string) => {
    setSelections(prev => ({
      ...prev,
      selectedAgents: prev.selectedAgents.filter(
        a => a.datasetId !== datasetId
      ),
      selectedRuns: prev.selectedRuns.filter(r => r.datasetId !== datasetId),
      activeDatasetId:
        prev.activeDatasetId === datasetId ? null : prev.activeDatasetId,
    }));
  }, []);

  const getSelectedAgentsForDataset = useCallback(
    (datasetId: string): string[] => {
      return selections.selectedAgents
        .filter(a => a.datasetId === datasetId)
        .map(a => a.agentName);
    },
    [selections.selectedAgents]
  );

  const getSelectedRunsForDataset = useCallback(
    (datasetId: string): string[] => {
      return selections.selectedRuns
        .filter(r => r.datasetId === datasetId)
        .map(r => r.runId);
    },
    [selections.selectedRuns]
  );

  const isAgentSelected = useCallback(
    (agentName: string, datasetId: string): boolean => {
      return selections.selectedAgents.some(
        a => a.agentName === agentName && a.datasetId === datasetId
      );
    },
    [selections.selectedAgents]
  );

  const isRunSelected = useCallback(
    (runId: string, datasetId: string): boolean => {
      return selections.selectedRuns.some(
        r => r.runId === runId && r.datasetId === datasetId
      );
    },
    [selections.selectedRuns]
  );

  return (
    <GlobalCompareContext.Provider
      value={{
        selections,
        selectAgent,
        deselectAgent,
        selectRun,
        deselectRun,
        clearAllSelections,
        clearDatasetSelections,
        getSelectedAgentsForDataset,
        getSelectedRunsForDataset,
        isAgentSelected,
        isRunSelected,
      }}
    >
      {children}
    </GlobalCompareContext.Provider>
  );
};
