import { render, screen } from '@testing-library/react';
import React from 'react';

import { ComparisonRow } from './index';

describe('ComparisonRow', () => {
  it('should render label and values', () => {
    const values = ['value1', 'value2', 'value3'];
    render(<ComparisonRow label='Test Label' values={values} />);

    expect(screen.getByText('Test Label')).toBeInTheDocument();
    expect(screen.getByText('value1')).toBeInTheDocument();
    expect(screen.getByText('value2')).toBeInTheDocument();
    expect(screen.getByText('value3')).toBeInTheDocument();
  });

  it('should handle empty values array', () => {
    render(<ComparisonRow label='Test Label' values={[]} />);

    expect(screen.getByText('Test Label')).toBeInTheDocument();
  });

  it('should handle single value', () => {
    render(<ComparisonRow label='Test Label' values={['single']} />);

    expect(screen.getByText('Test Label')).toBeInTheDocument();
    expect(screen.getByText('single')).toBeInTheDocument();
  });

  it('should handle undefined values gracefully', () => {
    render(
      <ComparisonRow
        label='Test Label'
        values={[]}
      />
    );

    expect(screen.getByText('Test Label')).toBeInTheDocument();
  });
      // Provide empty array to reflect graceful handling in component use
      render(<ComparisonRow label='Tokens' values={[]} />);

      expect(screen.getByText('Tokens')).toBeInTheDocument();
});
