import { render, screen } from '@testing-library/react';
import React from 'react';

import { StatusBadge } from './index';

describe('StatusBadge', () => {
  it('should render Success badge with correct styling', () => {
    render(<StatusBadge status='Success' />);
    const badge = screen.getByText('Success');
    expect(badge).toBeInTheDocument();
    expect(badge).toHaveClass('text-text-success');
  });

  it('should render Failure badge with correct styling', () => {
    render(<StatusBadge status='Failure' />);
    const badge = screen.getByText('Failure');
    expect(badge).toBeInTheDocument();
    expect(badge).toHaveClass('text-text-danger');
  });
});
