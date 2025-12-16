import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';

import TaskDetailsModal from './index';

jest.mock('@/components/base/ui/modal', () => ({
  __esModule: true,
  default: ({
    isOpen,
    onClose,
    title,
    children,
  }: {
    isOpen: boolean;
    onClose: () => void;
    title: string;
    children: React.ReactNode;
  }) =>
    isOpen ? (
      <div data-testid='modal'>
        <div>{title}</div>
        <button onClick={onClose}>Close</button>
        {children}
      </div>
    ) : null,
}));
jest.mock('@/components/base/codeViewer', () => ({
  __esModule: true,
  default: ({ code, language }: { code: string; language: string }) => (
    <div data-testid={`code-viewer-${language}`}>{code}</div>
  ),
}));
jest.mock('@/components/base/tacticInfo', () => ({
  __esModule: true,
  default: ({ tactics }: { tactics: unknown[] }) => (
    <div data-testid='tactic-info'>Tactics: {tactics.length}</div>
  ),
}));

describe('TaskDetailsModal', () => {
  it('should not render when closed', () => {
    render(
      <TaskDetailsModal
        isOpen={false}
        onClose={jest.fn()}
        details={{ key: 'value' }}
      />
    );

    expect(screen.queryByTestId('modal')).not.toBeInTheDocument();
  });

  it('should not render when details is null', () => {
    render(
      <TaskDetailsModal isOpen={true} onClose={jest.fn()} details={null} />
    );

    expect(screen.queryByTestId('modal')).not.toBeInTheDocument();
  });

  it('should render when open with details', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{ key: 'value' }}
      />
    );

    expect(screen.getByTestId('modal')).toBeInTheDocument();
    expect(screen.getByText('Task Details')).toBeInTheDocument();
  });

  it('should render custom title', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{ key: 'value' }}
        title='Custom Title'
      />
    );

    expect(screen.getByText('Custom Title')).toBeInTheDocument();
  });

  it('should render tabs for available keys', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{ key1: 'value1', key2: 'value2' }}
      />
    );

    expect(screen.getByText('key1')).toBeInTheDocument();
    expect(screen.getByText('key2')).toBeInTheDocument();
  });

  it('should switch tabs when clicked', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{ key1: 'value1', key2: 'value2' }}
      />
    );

    const tab2 = screen.getByText('key2');
    fireEvent.click(tab2);

    // Should show content for key2
    expect(screen.getByText(/value2/)).toBeInTheDocument();
  });

  it('should render cpp code for cpp_code key', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{ cpp_code: 'int main() {}' }}
      />
    );

    expect(screen.getByTestId('code-viewer-cpp')).toBeInTheDocument();
    expect(screen.getByText('int main() {}')).toBeInTheDocument();
  });

  it('should render cpp code for cppCode key', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{ cppCode: 'code' }}
      />
    );

    expect(screen.getByTestId('code-viewer-cpp')).toBeInTheDocument();
  });

  it('should render text for targetContent key', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{ targetContent: 'target text' }}
      />
    );

    expect(screen.getByTestId('code-viewer-text')).toBeInTheDocument();
  });

  it('should render text for lemmaContent key', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{ lemmaContent: 'lemma text' }}
      />
    );

    expect(screen.getByTestId('code-viewer-text')).toBeInTheDocument();
  });

  it('should render text for statesContent key', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{ statesContent: 'states text' }}
      />
    );

    expect(screen.getByTestId('code-viewer-text')).toBeInTheDocument();
  });

  it('should render tactic info for tactic key', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{
          tactic: [
            {
              goal: 'test',
              status: 'success',
              tactic_prediction_tactic: 'apply',
            },
          ],
        }}
      />
    );

    expect(screen.getByTestId('tactic-info')).toBeInTheDocument();
  });

  it('should render JSON content for non-custom keys', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{ custom_key: { data: 'value' } }}
      />
    );

    expect(screen.getByText(/data/)).toBeInTheDocument();
  });

  it('should handle array values in custom keys', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{ cpp_code: ['code1', 'code2'] }}
      />
    );

    expect(screen.getAllByTestId('code-viewer-cpp')).toHaveLength(2);
  });

  it('should handle string array values in json keys', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{ custom_array: ['str1', 'str2'] }}
      />
    );

    expect(screen.getByText(/Item 1/)).toBeInTheDocument();
    expect(screen.getByText(/Item 2/)).toBeInTheDocument();
  });

  it('should show no details message when no keys', () => {
    render(<TaskDetailsModal isOpen={true} onClose={jest.fn()} details={{}} />);

    expect(screen.getByText('No details available')).toBeInTheDocument();
  });

  it('should call onClose when close button is clicked', () => {
    const handleClose = jest.fn();
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={handleClose}
        details={{ key: 'value' }}
      />
    );

    fireEvent.click(screen.getByText('Close'));
    expect(handleClose).toHaveBeenCalled();
  });

  it('should handle string value in custom keys', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{ code: 'single string' }}
      />
    );

    expect(screen.getByTestId('code-viewer-cpp')).toBeInTheDocument();
  });

  it('should handle non-string array values in custom keys', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{ code: [1, 2, 3] }}
      />
    );

    // Should not render code viewer for non-string arrays
    expect(screen.queryByTestId('code-viewer-cpp')).not.toBeInTheDocument();
  });

  it('should handle empty string array in custom keys', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{ code: [] }}
      />
    );

    // Should not render code viewer for empty arrays
    expect(screen.queryByTestId('code-viewer-cpp')).not.toBeInTheDocument();
  });

  it('should handle string value in json keys', () => {
    render(
      <TaskDetailsModal
        isOpen={true}
        onClose={jest.fn()}
        details={{ json_key: 'string value' }}
      />
    );

    expect(screen.getByText('string value')).toBeInTheDocument();
  });
});
