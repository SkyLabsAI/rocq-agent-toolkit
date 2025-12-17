import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';

import { SlidingTabs } from './index';

describe('SlidingTabs', () => {
  const mockTabs = [
    { id: 'tab1', label: 'Tab 1' },
    { id: 'tab2', label: 'Tab 2' },
    { id: 'tab3', label: 'Tab 3' },
  ];

  it('should render tabs', () => {
    render(<SlidingTabs tabs={mockTabs} />);

    expect(screen.getByText('Tab 1')).toBeInTheDocument();
    expect(screen.getByText('Tab 2')).toBeInTheDocument();
    expect(screen.getByText('Tab 3')).toBeInTheDocument();
  });

  it('should set first tab as active by default', () => {
    render(<SlidingTabs tabs={mockTabs} />);

    const tab1 = screen.getByText('Tab 1');
    expect(tab1).toHaveClass('text-text');
  });

  it('should set defaultTab as active when provided', () => {
    render(<SlidingTabs tabs={mockTabs} defaultTab='tab2' />);

    const tab2 = screen.getByText('Tab 2');
    expect(tab2).toHaveClass('text-text');
  });

  it('should call onTabChange when tab is clicked', () => {
    const handleTabChange = jest.fn();
    render(<SlidingTabs tabs={mockTabs} onTabChange={handleTabChange} />);

    fireEvent.click(screen.getByText('Tab 2'));

    expect(handleTabChange).toHaveBeenCalledWith('tab2');
  });

  it('should not call onTabChange when clicking active tab', () => {
    const handleTabChange = jest.fn();
    render(
      <SlidingTabs
        tabs={mockTabs}
        defaultTab='tab1'
        onTabChange={handleTabChange}
      />
    );

    fireEvent.click(screen.getByText('Tab 1'));

    expect(handleTabChange).not.toHaveBeenCalled();
  });

  it('should render tabs with icons', () => {
    const tabsWithIcons = [
      {
        id: 'tab1',
        label: 'Tab 1',
        icon: <span data-testid='icon1'>Icon1</span>,
      },
      {
        id: 'tab2',
        label: 'Tab 2',
        icon: <span data-testid='icon2'>Icon2</span>,
      },
    ];

    render(<SlidingTabs tabs={tabsWithIcons} />);

    expect(screen.getByTestId('icon1')).toBeInTheDocument();
    expect(screen.getByTestId('icon2')).toBeInTheDocument();
  });

  it('should return null when tabs array is empty', () => {
    const { container } = render(<SlidingTabs tabs={[]} />);
    expect(container.firstChild).toBeNull();
  });

  it('should handle window resize', () => {
    render(<SlidingTabs tabs={mockTabs} />);

    // Trigger resize event
    window.dispatchEvent(new Event('resize'));

    // Component should still render
    expect(screen.getByText('Tab 1')).toBeInTheDocument();
  });
});
