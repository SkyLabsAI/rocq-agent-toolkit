import { render, screen } from '@testing-library/react';
import React from 'react';

import JsonContent from './json-content';

describe('JsonContent', () => {
  it('should render JSON string', () => {
    const value = { key: 'value', number: 123 };
    render(<JsonContent value={value} />);

    const pre = screen.getByText(/key/).closest('pre');
    expect(pre).toBeInTheDocument();
    expect(pre?.textContent).toContain('key');
    expect(pre?.textContent).toContain('value');
  });

  it('should render string value directly', () => {
    const value = 'simple string';
    render(<JsonContent value={value} />);

    expect(screen.getByText('simple string')).toBeInTheDocument();
  });

  it('should format complex objects', () => {
    const value = {
      nested: {
        array: [1, 2, 3],
        object: { key: 'value' },
      },
    };
    render(<JsonContent value={value} />);

    expect(screen.getByText(/nested/)).toBeInTheDocument();
    expect(screen.getByText(/array/)).toBeInTheDocument();
  });

  it('should handle null value', () => {
    render(<JsonContent value={null} />);

    expect(screen.getByText(/null/)).toBeInTheDocument();
  });

  it('should handle array value', () => {
    const value = [1, 2, 3];
    render(<JsonContent value={value} />);

    expect(screen.getByText(/\[/)).toBeInTheDocument();
    expect(screen.getByText(/\]/)).toBeInTheDocument();
  });
});
