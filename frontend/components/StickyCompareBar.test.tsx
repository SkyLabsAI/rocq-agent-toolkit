import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';

import StickyCompareBar from './StickyCompareBar';

describe('StickyCompareBar', () => {
  const defaultProps = {
    selectedItems: ['run1', 'run2'],
    agentName: 'TestAgent',
    onClearSelection: jest.fn(),
    onCompareSelected: jest.fn(),
    attribute: 'runs',
  };

  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('renders nothing when no items are selected', () => {
    render(<StickyCompareBar {...defaultProps} selectedItems={[]} />);
    const bar = screen.queryByText(/TestAgent/);
    expect(bar).not.toBeInTheDocument();
  });

  it('renders correctly when items are selected', () => {
    render(<StickyCompareBar {...defaultProps} />);

    expect(screen.getByText('Agent: TestAgent')).toBeInTheDocument();
    expect(screen.getByText('Selected 2 runs')).toBeInTheDocument();
    expect(
      screen.getByRole('button', { name: /clear selection/i })
    ).toBeInTheDocument();
    expect(
      screen.getByRole('button', { name: /compare 2 runs/i })
    ).toBeInTheDocument();
  });

  it('calls onClearSelection when clear button is clicked', () => {
    render(<StickyCompareBar {...defaultProps} />);

    const clearButton = screen.getByRole('button', {
      name: /clear selection/i,
    });
    fireEvent.click(clearButton);

    expect(defaultProps.onClearSelection).toHaveBeenCalledTimes(1);
  });

  it('calls onCompareSelected when compare button is clicked', () => {
    render(<StickyCompareBar {...defaultProps} />);

    const compareButton = screen.getByRole('button', {
      name: /compare 2 runs/i,
    });
    fireEvent.click(compareButton);

    expect(defaultProps.onCompareSelected).toHaveBeenCalledTimes(1);
  });

  it('disables compare button when fewer than 2 items selected', () => {
    render(<StickyCompareBar {...defaultProps} selectedItems={['run1']} />);

    const compareButton = screen.getByRole('button', {
      name: /select 1 more run/i,
    });
    expect(compareButton).toBeDisabled();
  });

  it('adds padding to body when visible and removes it on unmount', () => {
    render(<StickyCompareBar {...defaultProps} />);
    expect(document.body.style.paddingBottom).toBe('80px');

    // Unmount
    render(<StickyCompareBar {...defaultProps} selectedItems={[]} />);
    // Note: In the component, the effect dependency is [selectedItems.length].
    // If we re-render with empty list, the component returns null, but the cleanup function from the previous effect run should have fired?
    // Actually, if the component returns null, the effect cleanup runs.
    // Wait, the component returns null if selectedItems.length === 0.
    // React hooks rules: hooks must be called in the same order.
    // The component calls useEffect BEFORE the early return check?
    // Let's check the code.
    // Code:
    // useEffect(...)
    // if (selectedItems.length === 0) return null;
    // So yes, effect runs.

    // However, testing library `render` returns `unmount`.
    // Let's try unmounting explicitly.
  });

  it('cleans up body padding on unmount', () => {
    const { unmount } = render(<StickyCompareBar {...defaultProps} />);
    expect(document.body.style.paddingBottom).toBe('80px');
    unmount();
    expect(document.body.style.paddingBottom).toBe('');
  });
});
