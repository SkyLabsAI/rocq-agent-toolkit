import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';

import TacticInfoViewer, { type TacticObject } from './index';

jest.mock('../statusBadge', () => ({
  StatusBadge: ({ status }: { status: string }) => (
    <div data-testid={`status-${status}`}>{status}</div>
  ),
}));

describe('TacticInfoViewer', () => {
  const mockTactics: TacticObject[] = [
    {
      goal: 'Prove theorem 1',
      tactic_prediction_tactic: 'apply auto',
      status: 'success',
      tactic_prediction_explanation: 'Explanation 1',
      custom_field: 'custom value',
    },
    {
      goal: 'Prove theorem 2',
      tactic_prediction_tactic: 'apply simp',
      status: 'failure',
      tactic_prediction_explanation: 'Explanation 2',
      another_field: 123,
    },
  ];

  beforeEach(() => {
    jest.spyOn(console, 'warn').mockImplementation();
  });

  afterEach(() => {
    jest.restoreAllMocks();
  });

  it('should render tactics', () => {
    render(<TacticInfoViewer tactics={mockTactics} />);

    expect(screen.getByText('Prove theorem 1')).toBeInTheDocument();
    expect(screen.getByText('Prove theorem 2')).toBeInTheDocument();
  });

  it('should show empty state when no tactics', () => {
    render(<TacticInfoViewer tactics={[]} />);

    expect(
      screen.getByText('No tactic information available')
    ).toBeInTheDocument();
  });

  it('should render tactic prediction', () => {
    render(<TacticInfoViewer tactics={mockTactics} />);

    expect(screen.getByText('apply auto')).toBeInTheDocument();
    expect(screen.getByText('apply simp')).toBeInTheDocument();
  });

  it('should render explanation', () => {
    render(<TacticInfoViewer tactics={mockTactics} />);

    expect(screen.getByText('Explanation 1')).toBeInTheDocument();
    expect(screen.getByText('Explanation 2')).toBeInTheDocument();
  });

  it('should render status badges', () => {
    render(<TacticInfoViewer tactics={mockTactics} />);

    expect(screen.getByTestId('status-success')).toBeInTheDocument();
    expect(screen.getByTestId('status-failure')).toBeInTheDocument();
  });

  it('should render additional information section', () => {
    render(<TacticInfoViewer tactics={mockTactics} />);

    expect(screen.getByText('Additional Information')).toBeInTheDocument();
  });

  it('should toggle additional information', () => {
    render(<TacticInfoViewer tactics={mockTactics} />);

    const toggleButton = screen
      .getByText('Additional Information')
      .closest('div');
    if (toggleButton) {
      fireEvent.click(toggleButton);
      // Additional info should expand
    }
  });

  it('should render custom title', () => {
    render(<TacticInfoViewer tactics={mockTactics} title='Custom Title' />);

    expect(screen.getByText('Custom Title')).toBeInTheDocument();
  });

  it('should calculate success rate', () => {
    render(<TacticInfoViewer tactics={mockTactics} />);

    expect(screen.getByText(/Success Rate:/)).toBeInTheDocument();
    expect(screen.getByText('50.0%')).toBeInTheDocument();
  });

  it('should show total tactics count', () => {
    render(<TacticInfoViewer tactics={mockTactics} />);

    expect(screen.getByText(/Total Tactics:/)).toBeInTheDocument();
    expect(screen.getByText('2')).toBeInTheDocument();
  });

  it('should handle tactics without status', () => {
    const tacticsWithoutStatus: TacticObject[] = [
      {
        goal: 'Test',
        tactic_prediction_tactic: 'apply',
        tactic_prediction_explanation: 'explanation',
      },
    ];

    render(<TacticInfoViewer tactics={tacticsWithoutStatus} />);

    expect(screen.getByTestId('status-Not found')).toBeInTheDocument();
  });

  it('should handle "not found" status', () => {
    const tactics: TacticObject[] = [
      {
        goal: 'Test',
        tactic_prediction_tactic: 'apply',
        status: 'not found',
        tactic_prediction_explanation: 'explanation',
      },
    ];

    render(<TacticInfoViewer tactics={tactics} />);

    expect(screen.getByTestId('status-not found')).toBeInTheDocument();
  });

  it('should render additional keys', () => {
    render(<TacticInfoViewer tactics={mockTactics} />);

    const toggleButton = screen
      .getByText('Additional Information')
      .closest('div');
    if (toggleButton) {
      fireEvent.click(toggleButton);
      expect(screen.getByText(/custom field/i)).toBeInTheDocument();
      expect(screen.getByText(/another field/i)).toBeInTheDocument();
    }
  });

  it('should handle tactics without prediction tactic', () => {
    const tactics: TacticObject[] = [
      {
        goal: 'Test',
        tactic_prediction_explanation: 'explanation',
        status: 'success',
      },
    ];

    render(<TacticInfoViewer tactics={tactics} />);

    expect(screen.getByText('Test')).toBeInTheDocument();
  });

  it('should handle tactics without explanation', () => {
    const tactics: TacticObject[] = [
      {
        goal: 'Test',
        tactic_prediction_tactic: 'apply',
        status: 'success',
      },
    ];

    render(<TacticInfoViewer tactics={tactics} />);

    expect(screen.getByText('Test')).toBeInTheDocument();
  });

  it('should format additional field values as JSON when not string', () => {
    render(<TacticInfoViewer tactics={mockTactics} />);

    const toggleButton = screen
      .getByText('Additional Information')
      .closest('div');
    if (toggleButton) {
      fireEvent.click(toggleButton);
      // Should render number as JSON
      expect(screen.getByText('123')).toBeInTheDocument();
    }
  });
});
