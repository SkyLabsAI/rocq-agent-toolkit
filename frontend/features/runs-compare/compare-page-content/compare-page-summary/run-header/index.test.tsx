import { render, screen } from '@testing-library/react';
import React from 'react';

import { RunsHeader } from './index';

describe('RunsHeader', () => {
  it('should render title', () => {
    render(<RunsHeader title='Test Title' keys={[]} />);
    expect(screen.getByText('Test Title')).toBeInTheDocument();
  });

  it('should render keys', () => {
    const keys = ['Key1', 'Key2', 'Key3'];
    render(<RunsHeader title='Test Title' keys={keys} />);

    keys.forEach(key => {
      expect(screen.getByText(key)).toBeInTheDocument();
    });
  });

  it('should render with empty keys array', () => {
    render(<RunsHeader title='Test Title' keys={[]} />);
    expect(screen.getByText('Test Title')).toBeInTheDocument();
  });
});
