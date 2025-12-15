import { fireEvent, render, screen, waitFor } from '@testing-library/react';
import React from 'react';

import {
  GlobalCompareProvider,
  useGlobalCompare,
} from './GlobalCompareContext';

// Test component to access context
const TestComponent = () => {
  const {
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
  } = useGlobalCompare();

  return (
    <div>
      <div data-testid='agent-count'>{selections.selectedAgents.length}</div>
      <div data-testid='run-count'>{selections.selectedRuns.length}</div>
      <div data-testid='active-dataset'>
        {selections.activeDatasetId || 'none'}
      </div>
      <button onClick={() => selectAgent('agent1', 'dataset1')}>
        Select Agent
      </button>
      <button onClick={() => deselectAgent('agent1', 'dataset1')}>
        Deselect Agent
      </button>
      <button onClick={() => selectRun('run1', 'dataset1')}>Select Run</button>
      <button onClick={() => deselectRun('run1', 'dataset1')}>
        Deselect Run
      </button>
      <button onClick={clearAllSelections}>Clear All</button>
      <button onClick={() => clearDatasetSelections('dataset1')}>
        Clear Dataset
      </button>
      <div data-testid='agents-for-dataset1'>
        {getSelectedAgentsForDataset('dataset1').join(',')}
      </div>
      <div data-testid='runs-for-dataset1'>
        {getSelectedRunsForDataset('dataset1').join(',')}
      </div>
      <div data-testid='is-agent-selected'>
        {isAgentSelected('agent1', 'dataset1') ? 'yes' : 'no'}
      </div>
      <div data-testid='is-run-selected'>
        {isRunSelected('run1', 'dataset1') ? 'yes' : 'no'}
      </div>
    </div>
  );
};

describe('GlobalCompareContext', () => {
  it('should throw error when used outside provider', () => {
    const consoleError = jest.spyOn(console, 'error').mockImplementation();
    expect(() => render(<TestComponent />)).toThrow();
    consoleError.mockRestore();
  });

  it('should initialize with empty selections', () => {
    render(
      <GlobalCompareProvider>
        <TestComponent />
      </GlobalCompareProvider>
    );

    expect(screen.getByTestId('agent-count')).toHaveTextContent('0');
    expect(screen.getByTestId('run-count')).toHaveTextContent('0');
    expect(screen.getByTestId('active-dataset')).toHaveTextContent('none');
  });

  it('should select and deselect agents', async () => {
    render(
      <GlobalCompareProvider>
        <TestComponent />
      </GlobalCompareProvider>
    );

    fireEvent.click(screen.getByText('Select Agent'));

    await waitFor(() => {
      expect(screen.getByTestId('agent-count')).toHaveTextContent('1');
      expect(screen.getByTestId('is-agent-selected')).toHaveTextContent('yes');
    });

    fireEvent.click(screen.getByText('Deselect Agent'));

    await waitFor(() => {
      expect(screen.getByTestId('agent-count')).toHaveTextContent('0');
      expect(screen.getByTestId('is-agent-selected')).toHaveTextContent('no');
    });
  });

  it('should select and deselect runs', async () => {
    render(
      <GlobalCompareProvider>
        <TestComponent />
      </GlobalCompareProvider>
    );

    fireEvent.click(screen.getByText('Select Run'));

    await waitFor(() => {
      expect(screen.getByTestId('run-count')).toHaveTextContent('1');
      expect(screen.getByTestId('is-run-selected')).toHaveTextContent('yes');
    });

    fireEvent.click(screen.getByText('Deselect Run'));

    await waitFor(() => {
      expect(screen.getByTestId('run-count')).toHaveTextContent('0');
      expect(screen.getByTestId('is-run-selected')).toHaveTextContent('no');
    });
  });

  it('should clear all selections', async () => {
    render(
      <GlobalCompareProvider>
        <TestComponent />
      </GlobalCompareProvider>
    );

    fireEvent.click(screen.getByText('Select Agent'));
    fireEvent.click(screen.getByText('Select Run'));

    await waitFor(() => {
      expect(screen.getByTestId('agent-count')).toHaveTextContent('1');
      expect(screen.getByTestId('run-count')).toHaveTextContent('1');
    });

    fireEvent.click(screen.getByText('Clear All'));

    await waitFor(() => {
      expect(screen.getByTestId('agent-count')).toHaveTextContent('0');
      expect(screen.getByTestId('run-count')).toHaveTextContent('0');
    });
  });

  it('should clear dataset-specific selections', async () => {
    render(
      <GlobalCompareProvider>
        <TestComponent />
      </GlobalCompareProvider>
    );

    fireEvent.click(screen.getByText('Select Agent'));
    fireEvent.click(screen.getByText('Select Run'));

    await waitFor(() => {
      expect(screen.getByTestId('agent-count')).toHaveTextContent('1');
    });

    fireEvent.click(screen.getByText('Clear Dataset'));

    await waitFor(() => {
      expect(screen.getByTestId('agent-count')).toHaveTextContent('0');
      expect(screen.getByTestId('run-count')).toHaveTextContent('0');
    });
  });

  it('should get selected agents for dataset', async () => {
    render(
      <GlobalCompareProvider>
        <TestComponent />
      </GlobalCompareProvider>
    );

    fireEvent.click(screen.getByText('Select Agent'));

    await waitFor(() => {
      expect(screen.getByTestId('agents-for-dataset1')).toHaveTextContent(
        'agent1'
      );
    });
  });

  it('should get selected runs for dataset', async () => {
    render(
      <GlobalCompareProvider>
        <TestComponent />
      </GlobalCompareProvider>
    );

    fireEvent.click(screen.getByText('Select Run'));

    await waitFor(() => {
      expect(screen.getByTestId('runs-for-dataset1')).toHaveTextContent('run1');
    });
  });
});
