import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';

import { TaskRow } from './index';

describe('TaskRow', () => {
  it('should render stats', () => {
    const stats = ['run1', 10, '80.00', 50, 5000, '2.50'];
    const handleClick = jest.fn();

    render(<TaskRow stats={stats} onClick={handleClick} />);

    expect(screen.getByText('run1')).toBeInTheDocument();
    expect(screen.getByText('10')).toBeInTheDocument();
    expect(screen.getByText('80.00')).toBeInTheDocument();
  });

  it('should call onClick when remove button is clicked', () => {
    const stats = ['run1', 10, '80.00', 50, 5000, '2.50'];
    const handleClick = jest.fn();

    render(<TaskRow stats={stats} onClick={handleClick} />);

    const removeButton = screen.getByText('Remove');
    fireEvent.click(removeButton);

    expect(handleClick).toHaveBeenCalledTimes(1);
  });

  it('should render first stat with different styling', () => {
    const stats = ['run1', 10];
    const handleClick = jest.fn();

    render(<TaskRow stats={stats} onClick={handleClick} />);

    expect(screen.getByText('run1')).toBeInTheDocument();
    expect(screen.getByText('10')).toBeInTheDocument();
  });
});
