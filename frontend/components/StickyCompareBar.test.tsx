import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';

import StickyCompareBar from './sticky-compare-bar';

// Mock createPortal to render in the same container
jest.mock('react-dom', () => ({
  ...jest.requireActual('react-dom'),
  createPortal: (node: React.ReactNode) => node,
}));

describe('StickyCompareBar component', () => {
  const defaultProps = {
    selectedItems: ['item-1', 'item-2'],
    onClearSelection: jest.fn(),
    onCompareSelected: jest.fn(),
    attribute: 'Runs',
  };

  beforeEach(() => {
    jest.clearAllMocks();
  });

  describe('Visibility', () => {
    it('should render when items are selected', () => {
      render(<StickyCompareBar {...defaultProps} />);
      expect(screen.getByText('Selected 2 Runs')).toBeInTheDocument();
    });

    it('should not render when no items selected', () => {
      render(<StickyCompareBar {...defaultProps} selectedItems={[]} />);
      expect(screen.queryByText('Selected')).not.toBeInTheDocument();
    });

    it('should render with single item selected', () => {
      render(<StickyCompareBar {...defaultProps} selectedItems={['item-1']} />);
      expect(screen.getByText('Selected 1 Runs')).toBeInTheDocument();
    });
  });

  describe('Item count display', () => {
    it('should display correct count for 2 items', () => {
      render(<StickyCompareBar {...defaultProps} selectedItems={['a', 'b']} />);
      expect(screen.getByText('Selected 2 Runs')).toBeInTheDocument();
    });

    it('should display correct count for 5 items', () => {
      render(
        <StickyCompareBar
          {...defaultProps}
          selectedItems={['a', 'b', 'c', 'd', 'e']}
        />
      );
      expect(screen.getByText('Selected 5 Runs')).toBeInTheDocument();
    });
  });

  describe('Attribute display', () => {
    it('should display correct attribute name', () => {
      render(<StickyCompareBar {...defaultProps} attribute='Agents' />);
      expect(screen.getByText('Selected 2 Agents')).toBeInTheDocument();
    });
  });

  describe('Compare button', () => {
    it('should be disabled when less than 2 items selected', () => {
      render(<StickyCompareBar {...defaultProps} selectedItems={['item-1']} />);
      const compareButton = screen.getByText('Select 1 more Runs');
      expect(compareButton.closest('button')).toBeDisabled();
    });

    it('should be enabled when 2 or more items selected', () => {
      render(<StickyCompareBar {...defaultProps} selectedItems={['a', 'b']} />);
      const compareButton = screen.getByText('Compare 2 Runs');
      expect(compareButton.closest('button')).not.toBeDisabled();
    });

    it('should show "Select 1 more" message when only 1 item', () => {
      render(<StickyCompareBar {...defaultProps} selectedItems={['item-1']} />);
      expect(screen.getByText('Select 1 more Runs')).toBeInTheDocument();
    });

    it('should show "Compare X" when 2+ items selected', () => {
      render(
        <StickyCompareBar {...defaultProps} selectedItems={['a', 'b', 'c']} />
      );
      expect(screen.getByText('Compare 3 Runs')).toBeInTheDocument();
    });

    it('should call onCompareSelected when clicked', () => {
      const onCompareSelected = jest.fn();
      render(
        <StickyCompareBar
          {...defaultProps}
          onCompareSelected={onCompareSelected}
        />
      );

      fireEvent.click(screen.getByText('Compare 2 Runs'));
      expect(onCompareSelected).toHaveBeenCalledTimes(1);
    });
  });

  describe('Clear button', () => {
    it('should call onClearSelection when clicked', () => {
      const onClearSelection = jest.fn();
      render(
        <StickyCompareBar
          {...defaultProps}
          onClearSelection={onClearSelection}
        />
      );

      fireEvent.click(screen.getByText('Clear Selection'));
      expect(onClearSelection).toHaveBeenCalledTimes(1);
    });
  });

  describe('Click propagation', () => {
    it('should stop propagation on clear button click', () => {
      const onClearSelection = jest.fn();
      const parentClickHandler = jest.fn();

      render(
        <div onClick={parentClickHandler}>
          <StickyCompareBar
            {...defaultProps}
            onClearSelection={onClearSelection}
          />
        </div>
      );

      fireEvent.click(screen.getByText('Clear Selection'));
      expect(onClearSelection).toHaveBeenCalled();
      // Parent should not receive the click due to stopPropagation
    });

    it('should stop propagation on compare button click', () => {
      const onCompareSelected = jest.fn();
      const parentClickHandler = jest.fn();

      render(
        <div onClick={parentClickHandler}>
          <StickyCompareBar
            {...defaultProps}
            onCompareSelected={onCompareSelected}
          />
        </div>
      );

      fireEvent.click(screen.getByText('Compare 2 Runs'));
      expect(onCompareSelected).toHaveBeenCalled();
    });
  });
});
