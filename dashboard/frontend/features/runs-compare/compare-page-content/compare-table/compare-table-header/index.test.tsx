import { render, screen } from '@testing-library/react';
import React from 'react';

import { type RunDetailsResponse } from '@/types/types';

import { getCommonGridStyle, TaskComparisonHeaderTop } from './index';

describe('TaskComparisonHeaderTop', () => {
  const mockRuns: RunDetailsResponse[] = [
    {
      run_id: 'run1',
      agent_name: 'agent1',
      total_tasks: 1,
      tasks: [],
    },
    {
      run_id: 'run2',
      agent_name: 'agent2',
      total_tasks: 1,
      tasks: [],
    },
  ];

  it('should render header with runs', () => {
    render(<TaskComparisonHeaderTop runs={mockRuns} />);

    expect(screen.getByText('Taskwise Comparison')).toBeInTheDocument();
    expect(screen.getByText('run1')).toBeInTheDocument();
    expect(screen.getByText('run2')).toBeInTheDocument();
  });

  it('should handle empty runs array', () => {
    render(<TaskComparisonHeaderTop runs={[]} />);

    expect(screen.getByText('Taskwise Comparison')).toBeInTheDocument();
  });
});

describe('getCommonGridStyle', () => {
  it('should return grid style with correct columns', () => {
    const style = getCommonGridStyle(3);

    expect(style.display).toBe('grid');
    expect(style.gridTemplateColumns).toBe(
      '350px repeat(3, minmax(0, 1fr)) 165px'
    );
    expect(style.alignItems).toBe('center');
    expect(style.columnGap).toBe('1rem');
  });

  it('should handle zero run count', () => {
    const style = getCommonGridStyle(0);

    expect(style.gridTemplateColumns).toBe(
      '350px repeat(0, minmax(0, 1fr)) 165px'
    );
  });
});
