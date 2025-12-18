import { render, screen } from '@testing-library/react';
import React from 'react';
import { MemoryRouter } from 'react-router-dom';

import { CompareRunsHeader } from './index';

describe('CompareRunsHeader', () => {
  it('should render title', () => {
    render(
      <MemoryRouter>
        <CompareRunsHeader title='Test Title' />
      </MemoryRouter>
    );

    expect(screen.getByText('Test Title')).toBeInTheDocument();
  });

  it('should render secondary text when provided', () => {
    render(
      <MemoryRouter>
        <CompareRunsHeader title='Test Title' secondary='Secondary Text' />
      </MemoryRouter>
    );

    expect(screen.getByText('Secondary Text')).toBeInTheDocument();
  });

  it('should render back link', () => {
    render(
      <MemoryRouter>
        <CompareRunsHeader title='Test Title' />
      </MemoryRouter>
    );

    const link = screen.getByRole('link');
    expect(link).toHaveAttribute('href', '/');
  });

  it('should not render secondary text when not provided', () => {
    render(
      <MemoryRouter>
        <CompareRunsHeader title='Test Title' />
      </MemoryRouter>
    );

    // Secondary text should be empty string, so we check it's not visible
    const secondary = screen.queryByText('Secondary Text');
    expect(secondary).not.toBeInTheDocument();
  });
});
