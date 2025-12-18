import { render, screen } from '@testing-library/react';
import React from 'react';
import { MemoryRouter } from 'react-router-dom';

import AgentCompareTable from './index';

jest.mock('./agent-compare-content', () => ({
  AgentCompareContent: () => (
    <div data-testid='agent-compare-content'>Agent Compare Content</div>
  ),
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

describe('AgentCompareTable', () => {
  it('should render with layout and title', () => {
    render(
      <MemoryRouter>
        <AgentCompareTable />
      </MemoryRouter>
    );

    expect(screen.getByText('Compare Agents')).toBeInTheDocument();
  });

  it('should render AgentCompareContent in Suspense', () => {
    render(
      <MemoryRouter>
        <AgentCompareTable />
      </MemoryRouter>
    );

    expect(screen.getByTestId('agent-compare-content')).toBeInTheDocument();
  });
});
