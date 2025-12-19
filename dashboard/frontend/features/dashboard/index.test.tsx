import { render, screen } from '@testing-library/react';
import React from 'react';
import { MemoryRouter } from 'react-router-dom';

import Dashboard from './index';

jest.mock('./agent-table', () => ({
  __esModule: true,
  default: () => <div data-testid='agent-table'>Agent Table</div>,
}));
jest.mock('@/layouts/common', () => {
  return function Layout({
    children,
    title,
  }: {
    children: React.ReactNode;
    title: string;
  }) {
    return (
      <div>
        <h1>{title}</h1>
        {children}
      </div>
    );
  };
});

describe('Dashboard', () => {
  it('should render with layout and title', () => {
    render(
      <MemoryRouter>
        <Dashboard />
      </MemoryRouter>
    );

    expect(screen.getByText('RAT Dashboard')).toBeInTheDocument();
  });

  it('should render AgentTable', () => {
    render(
      <MemoryRouter>
        <Dashboard />
      </MemoryRouter>
    );

    expect(screen.getByTestId('agent-table')).toBeInTheDocument();
  });
});
