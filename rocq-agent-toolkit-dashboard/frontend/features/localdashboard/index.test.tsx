import { render, screen } from '@testing-library/react';
import React from 'react';
import { MemoryRouter } from 'react-router-dom';

import LocalDashboard from './index';

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

describe('LocalDashboard', () => {
  it('should render with layout and title', () => {
    render(
      <MemoryRouter>
        <LocalDashboard />
      </MemoryRouter>
    );

    expect(screen.getByText('Internal Dashboard')).toBeInTheDocument();
  });

  it('should render AgentTable', () => {
    render(
      <MemoryRouter>
        <LocalDashboard />
      </MemoryRouter>
    );

    expect(screen.getByTestId('agent-table')).toBeInTheDocument();
  });
});
