import { render } from '@testing-library/react';
import TaskDetailsModal from '../index';

// Mock the components
jest.mock('@/components/base/modal', () => {
  return function MockModal({ children, isOpen }: { children: React.ReactNode; isOpen: boolean }) {
    return isOpen ? <div data-testid="modal">{children}</div> : null;
  };
});

jest.mock('@/components/base/codeViewer', () => {
  return function MockCodeViewer({ code }: { code: string }) {
    return <div data-testid="code-viewer">{code}</div>;
  };
});

jest.mock('@/components/base/tacticSteps', () => {
  return function MockTacticStepsViewer({ steps, type, title }: { steps: string[]; type: string; title: string }) {
    return (
      <div data-testid={`tactic-steps-${type}`}>
        <div>{title}</div>
        <div>{steps.length} steps</div>
      </div>
    );
  };
});

describe('TaskDetailsModal with Tactic Prediction', () => {
  const mockDetails = {
    tactic_prediction_explanation: [
      "Applying a minimal loop invariant to symbolically execute the for-loop in the goal.",
      "Strengthen the for-loop invariant to track sum and i and preserve the arithmetic relation 2*s = k*(k-1).",
      "The current goal is a pure arithmetic assertion from the loop invariant preservation",
      "No clear structural pattern applies and the last tactic was not go, so we escalate with go to resume automation."
    ],
    tactic_prediction_tactic: [
      "wp for (fun _ => emp)%Z; go.",
      "wp for (fun p => exists k s, __local p \\\"i\\\" |-> intr 15m k ** __local p \\\"sum\\\" |-> intr 15m s ** [| 2 * s = k * (k - 1) |]%Z; go.",
      "iPureIntro; try lia.",
      "go."
    ],
    other_data: "some other content"
  };

  it('should render tactic prediction explanation steps', () => {
    const { container } = render(
      <TaskDetailsModal
        isOpen={true}
        onClose={() => {}}
        details={mockDetails}
        taskId="test-task-123"
        title="Test Modal"
      />
    );

    expect(container.querySelector('[data-testid="tactic-steps-explanation"]')).toBeTruthy();
    expect(container.textContent).toContain('4 steps');
  });

  it('should have tactic prediction tabs available', () => {
    const { container } = render(
      <TaskDetailsModal
        isOpen={true}
        onClose={() => {}}
        details={mockDetails}
        title="Test Modal"
        taskId="test-task-456"
      />
    );

    // Should have tabs for both tactic prediction keys
    expect(container.textContent).toContain('tactic_prediction_explanation');
    expect(container.textContent).toContain('tactic_prediction_tactic');
  });

  it('should handle missing tactic prediction data gracefully', () => {
    const { container } = render(
      <TaskDetailsModal
        isOpen={true}
        onClose={() => {}}
        details={{ other_data: "just some data" }}
        title="Test Modal"
        taskId="test-task-789"
      />
    );

    expect(container.querySelector('[data-testid="tactic-steps-explanation"]')).toBeFalsy();
    expect(container.querySelector('[data-testid="tactic-steps-tactic"]')).toBeFalsy();
  });
});