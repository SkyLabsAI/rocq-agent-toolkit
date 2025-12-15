import { render, screen } from '@testing-library/react';
import React from 'react';

import CodeViewer from './index';

// Mock react-syntax-highlighter
jest.mock('react-syntax-highlighter', () => ({
  Prism: {
    as: jest.fn(() => {
      return function MockSyntaxHighlighter({
        children,
        language,
      }: {
        children: string;
        language: string;
      }) {
        return (
          <pre data-testid='syntax-highlighter' data-language={language}>
            {children}
          </pre>
        );
      };
    }),
  },
}));

jest.mock('react-syntax-highlighter/dist/esm/styles/prism', () => ({
  vscDarkPlus: {},
}));

describe('CodeViewer', () => {
  it('should render code', () => {
    render(<CodeViewer code='int main() { return 0; }' language='cpp' />);

    expect(screen.getByTestId('syntax-highlighter')).toBeInTheDocument();
    expect(screen.getByText('int main() { return 0; }')).toBeInTheDocument();
  });

  it('should render filename when provided', () => {
    render(<CodeViewer code='test code' language='cpp' filename='test.cpp' />);

    expect(screen.getByText('test.cpp')).toBeInTheDocument();
    expect(screen.getByText('(cpp)')).toBeInTheDocument();
  });

  it('should not render filename section when filename is not provided', () => {
    render(<CodeViewer code='test code' language='cpp' />);

    expect(screen.queryByText('test.cpp')).not.toBeInTheDocument();
  });

  it('should render with cpp language', () => {
    render(<CodeViewer code='code' language='cpp' />);

    expect(screen.getByTestId('syntax-highlighter')).toBeInTheDocument();
    expect(screen.getByText('code')).toBeInTheDocument();
  });

  it('should render with c++ language', () => {
    render(<CodeViewer code='code' language='c++' />);

    expect(screen.getByTestId('syntax-highlighter')).toBeInTheDocument();
    expect(screen.getByText('code')).toBeInTheDocument();
  });

  it('should render with text language', () => {
    render(<CodeViewer code='plain text' language='text' />);

    expect(screen.getByTestId('syntax-highlighter')).toBeInTheDocument();
    expect(screen.getByText('plain text')).toBeInTheDocument();
  });

  it('should render with unknown language', () => {
    render(<CodeViewer code='code' language='python' />);

    expect(screen.getByTestId('syntax-highlighter')).toBeInTheDocument();
    expect(screen.getByText('code')).toBeInTheDocument();
  });
});
