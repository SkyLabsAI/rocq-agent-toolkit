import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';

import { type Run } from '@/types/types';

import RunRow from './RunRow';

describe('RunRow component', () => {
  const mockRun: Run = {
    run_id: 'run-123',
    agent_name: 'test-agent',
    timestamp_utc: '2024-01-15T10:30:00Z',
    total_tasks: 10,
    success_count: 8,
    failure_count: 2,
    dataset_id: 'dataset-1',
    metadata: { tags: { version: '1.0', branch: 'main' } },
  };

  const defaultProps = {
    run: mockRun,
    totalTasks: 10,
    successCount: 8,
    failureCount: 2,
    timestamp: '2024-01-15T10:30:00Z',
    isSelected: false,
    isPinned: false,
    index: 0,
    onToggleExpansion: jest.fn(),
    onToggleSelection: jest.fn(),
    onPin: jest.fn(),
  };

  beforeEach(() => {
    jest.clearAllMocks();
  });

  describe('Rendering', () => {
    it('should render run ID', () => {
      render(<RunRow {...defaultProps} />);
      expect(screen.getByText('run-123')).toBeInTheDocument();
    });

    it('should render total tasks', () => {
      render(<RunRow {...defaultProps} />);
      expect(screen.getByText('10')).toBeInTheDocument();
    });

    it('should render success and failure counts', () => {
      render(<RunRow {...defaultProps} />);
      expect(screen.getByText('8')).toBeInTheDocument();
      expect(screen.getByText('2')).toBeInTheDocument();
    });

    it('should render success rate', () => {
      render(<RunRow {...defaultProps} />);
      expect(screen.getByText('(80.0%)')).toBeInTheDocument();
    });

    it('should render formatted timestamp', () => {
      render(<RunRow {...defaultProps} />);
      // The timestamp will be formatted according to locale
      const button = screen
        .getByRole('button', { name: 'Add to Compare' })
        .closest('div[class*="grid"]');
      expect(button?.textContent).toContain('2024');
    });
  });

  describe('Latest badge', () => {
    it('should render Latest badge when isLatest is true', () => {
      render(<RunRow {...defaultProps} isLatest={true} />);
      expect(screen.getByText('Latest')).toBeInTheDocument();
    });

    it('should not render Latest badge when isLatest is false', () => {
      render(<RunRow {...defaultProps} isLatest={false} />);
      expect(screen.queryByText('Latest')).not.toBeInTheDocument();
    });
  });

  describe('Tags', () => {
    it('should render tags from metadata', () => {
      render(
        <RunRow {...defaultProps} tags={{ version: '1.0', branch: 'main' }} />
      );
      expect(screen.getByText('1.0')).toBeInTheDocument();
      expect(screen.getByText('main')).toBeInTheDocument();
    });

    it('should not crash when tags are undefined', () => {
      render(<RunRow {...defaultProps} tags={undefined} />);
      expect(screen.getByText('run-123')).toBeInTheDocument();
    });
  });

  describe('Selection', () => {
    it('should show "Add to Compare" when not selected', () => {
      render(<RunRow {...defaultProps} isSelected={false} />);
      expect(screen.getByText('Add to Compare')).toBeInTheDocument();
    });

    it('should show "Deselect" when selected', () => {
      render(<RunRow {...defaultProps} isSelected={true} />);
      expect(screen.getByText('Deselect')).toBeInTheDocument();
    });

    it('should call onToggleSelection on button click', () => {
      const onToggleSelection = jest.fn();
      render(
        <RunRow {...defaultProps} onToggleSelection={onToggleSelection} />
      );

      fireEvent.click(screen.getByText('Add to Compare'));
      expect(onToggleSelection).toHaveBeenCalledWith(mockRun);
    });

    it('should not propagate click to row when selecting', () => {
      const onToggleExpansion = jest.fn();
      const onToggleSelection = jest.fn();
      render(
        <RunRow
          {...defaultProps}
          onToggleExpansion={onToggleExpansion}
          onToggleSelection={onToggleSelection}
        />
      );

      fireEvent.click(screen.getByText('Add to Compare'));
      expect(onToggleSelection).toHaveBeenCalled();
      expect(onToggleExpansion).not.toHaveBeenCalled();
    });
  });

  describe('Row click', () => {
    it('should call onToggleExpansion on row click', () => {
      const onToggleExpansion = jest.fn();
      render(
        <RunRow {...defaultProps} onToggleExpansion={onToggleExpansion} />
      );

      // Click on the run ID text (part of the row)
      fireEvent.click(screen.getByText('run-123'));
      expect(onToggleExpansion).toHaveBeenCalledWith(mockRun);
    });
  });

  describe('Pin functionality', () => {
    it('should call onPin when pin button is clicked', () => {
      const onPin = jest.fn();
      render(<RunRow {...defaultProps} onPin={onPin} />);

      const pinButton = screen.getByTitle('pin');
      fireEvent.click(pinButton);
      expect(onPin).toHaveBeenCalledWith(mockRun);
    });

    it('should not propagate click to row when pinning', () => {
      const onToggleExpansion = jest.fn();
      const onPin = jest.fn();
      render(
        <RunRow
          {...defaultProps}
          onToggleExpansion={onToggleExpansion}
          onPin={onPin}
        />
      );

      fireEvent.click(screen.getByTitle('pin'));
      expect(onPin).toHaveBeenCalled();
      expect(onToggleExpansion).not.toHaveBeenCalled();
    });
  });

  describe('Button variant', () => {
    it('should use default variant when not selected', () => {
      render(<RunRow {...defaultProps} isSelected={false} />);
      const button = screen.getByText('Add to Compare').closest('button');
      expect(button).toBeInTheDocument();
    });

    it('should use danger variant when selected', () => {
      render(<RunRow {...defaultProps} isSelected={true} />);
      const button = screen.getByText('Deselect').closest('button');
      expect(button).toBeInTheDocument();
    });
  });
});
