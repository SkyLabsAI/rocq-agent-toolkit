import { render, screen } from '@testing-library/react';
import React from 'react';

import CodeContent from './CodeContent';

jest.mock('@/components/base/codeViewer', () => ({
  __esModule: true,
  default: ({
    code,
    language,
    filename,
  }: {
    code: string;
    language: string;
    filename: string;
  }) => (
    <div data-testid='code-viewer'>
      <div data-testid='code'>{code}</div>
      <div data-testid='language'>{language}</div>
      <div data-testid='filename'>{filename}</div>
    </div>
  ),
}));

describe('CodeContent', () => {
  it('should render code with cpp language for cpp keys', () => {
    const values = ['int main() { return 0; }', 'void test() {}'];
    render(<CodeContent keyName='cpp_code' values={values} />);

    expect(screen.getAllByTestId('code-viewer')).toHaveLength(2);
    expect(screen.getAllByTestId('language')[0]).toHaveTextContent('cpp');
    expect(screen.getAllByTestId('filename')[0]).toHaveTextContent(
      'cpp_code_1.cpp'
    );
  });

  it('should render code with text language for non-cpp keys', () => {
    const values = ['some text content'];
    render(<CodeContent keyName='targetContent' values={values} />);

    expect(screen.getByTestId('language')).toHaveTextContent('text');
    expect(screen.getByTestId('filename')).toHaveTextContent(
      'targetContent_1.txt'
    );
  });

  it('should handle multiple code values', () => {
    const values = ['code1', 'code2', 'code3'];
    render(<CodeContent keyName='test_code' values={values} />);

    expect(screen.getAllByTestId('code-viewer')).toHaveLength(3);
    expect(screen.getAllByTestId('code')[0]).toHaveTextContent('code1');
    expect(screen.getAllByTestId('code')[1]).toHaveTextContent('code2');
    expect(screen.getAllByTestId('code')[2]).toHaveTextContent('code3');
  });

  it('should handle empty values array', () => {
    render(<CodeContent keyName='test' values={[]} />);

    expect(screen.queryByTestId('code-viewer')).not.toBeInTheDocument();
  });
});
