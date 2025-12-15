import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';
import { MemoryRouter } from 'react-router-dom';

import AgentTable from './AgentTable';

jest.mock('./agentview', () => ({
  __esModule: true,
  default: () => <div data-testid='agent-view'>Agent View</div>,
}));
jest.mock('./dataview', () => ({
  __esModule: true,
  default: () => <div data-testid='data-view'>Data View</div>,
}));

describe('AgentTable', () => {
  it('should render with default agents tab', () => {
    render(
      <MemoryRouter>
        <AgentTable />
      </MemoryRouter>
    );

    expect(screen.getByText('Leader Dashboard')).toBeInTheDocument();
    expect(screen.getByTestId('agent-view')).toBeInTheDocument();
    expect(screen.queryByTestId('data-view')).not.toBeInTheDocument();
  });

  it('should switch to datasets tab when clicked', () => {
    render(
      <MemoryRouter>
        <AgentTable />
      </MemoryRouter>
    );

    const datasetsTab = screen.getByText('Datasets');
    fireEvent.click(datasetsTab);

    expect(screen.getByTestId('data-view')).toBeInTheDocument();
    expect(screen.queryByTestId('agent-view')).not.toBeInTheDocument();
  });

  it('should render refresh button', () => {
    render(
      <MemoryRouter>
        <AgentTable />
      </MemoryRouter>
    );

    expect(screen.getByText('Refresh Data')).toBeInTheDocument();
  });
});
