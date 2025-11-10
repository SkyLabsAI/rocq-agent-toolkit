import { render } from '@testing-library/react';
import TacticStepsViewer from '../index';

// Mock react-syntax-highlighter
jest.mock('react-syntax-highlighter', () => ({
  Prism: ({ children }: { children: string }) => <pre>{children}</pre>
}));

jest.mock('react-syntax-highlighter/dist/esm/styles/prism', () => ({
  vscDarkPlus: {}
}));

describe('TacticStepsViewer', () => {
  const mockExplanationSteps = [
    "Applying a minimal loop invariant to symbolically execute the for-loop in the goal.",
    "Strengthen the for-loop invariant to track sum and i and preserve the arithmetic relation 2*s = k*(k-1).",
  ];

  const mockTacticSteps = [
    "wp for (fun _ => emp)%Z; go.",
    "iPureIntro; try lia.",
  ];

  it('should render explanation steps correctly', () => {
    const { container } = render(
      <TacticStepsViewer 
        steps={mockExplanationSteps}
        type="explanation"
        title="Test Explanation"
      />
    );
    
    expect(container.querySelector('.text-blue-400')).toBeTruthy();
    expect(container.textContent).toContain('Test Explanation');
    expect(container.textContent).toContain('2 steps');
  });

  it('should render tactic steps correctly', () => {
    const { container } = render(
      <TacticStepsViewer 
        steps={mockTacticSteps}
        type="tactic"
        title="Test Tactics"
      />
    );
    
    expect(container.querySelector('.text-green-400')).toBeTruthy();
    expect(container.textContent).toContain('Test Tactics');
    expect(container.textContent).toContain('2 steps');
  });

  it('should handle empty steps array', () => {
    const { container } = render(
      <TacticStepsViewer 
        steps={[]}
        type="explanation"
        title="Empty Test"
      />
    );
    
    expect(container.textContent).toContain('No explanation steps available');
  });
});