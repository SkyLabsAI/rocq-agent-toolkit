import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';

import { Button } from './index';

describe('Button component', () => {
  describe('Rendering', () => {
    it('should render children correctly', () => {
      render(<Button>Click me</Button>);
      expect(screen.getByText('Click me')).toBeInTheDocument();
    });

    it('should render as a button element', () => {
      render(<Button>Test</Button>);
      expect(screen.getByRole('button')).toBeInTheDocument();
    });
  });

  describe('Variants', () => {
    it('should apply default variant styles', () => {
      render(<Button variant='default'>Default</Button>);
      const button = screen.getByRole('button');
      expect(button).toHaveClass('bg-background-accent-gray-subtlest');
    });

    it('should apply ghost variant styles', () => {
      render(<Button variant='ghost'>Ghost</Button>);
      const button = screen.getByRole('button');
      expect(button).toHaveClass('border-transparent');
    });

    it('should apply danger variant styles', () => {
      render(<Button variant='danger'>Danger</Button>);
      const button = screen.getByRole('button');
      expect(button).toHaveClass('bg-background-danger');
      expect(button).toHaveClass('text-text-danger');
    });

    it('should apply outline variant styles', () => {
      render(<Button variant='outline'>Outline</Button>);
      const button = screen.getByRole('button');
      expect(button).toHaveClass('border-background-accent-gray-subtler');
    });
  });

  describe('Icons', () => {
    it('should render left icon', () => {
      render(
        <Button leftIcon={<span data-testid='left-icon'>←</span>}>
          With Icon
        </Button>
      );
      expect(screen.getByTestId('left-icon')).toBeInTheDocument();
    });

    it('should render right icon', () => {
      render(
        <Button rightIcon={<span data-testid='right-icon'>→</span>}>
          With Icon
        </Button>
      );
      expect(screen.getByTestId('right-icon')).toBeInTheDocument();
    });

    it('should render both icons', () => {
      render(
        <Button
          leftIcon={<span data-testid='left-icon'>←</span>}
          rightIcon={<span data-testid='right-icon'>→</span>}
        >
          Both Icons
        </Button>
      );
      expect(screen.getByTestId('left-icon')).toBeInTheDocument();
      expect(screen.getByTestId('right-icon')).toBeInTheDocument();
    });
  });

  describe('Dividers', () => {
    it('should render left divider when leftDivider is true', () => {
      const { container } = render(<Button leftDivider>With Divider</Button>);
      const divider = container.querySelector('.bg-border-bold');
      expect(divider).toBeInTheDocument();
    });

    it('should render right divider when rightDivider is true', () => {
      const { container } = render(<Button rightDivider>With Divider</Button>);
      const divider = container.querySelector('.bg-border-bold');
      expect(divider).toBeInTheDocument();
    });
  });

  describe('Interactions', () => {
    it('should call onClick handler when clicked', () => {
      const handleClick = jest.fn();
      render(<Button onClick={handleClick}>Click me</Button>);

      fireEvent.click(screen.getByRole('button'));
      expect(handleClick).toHaveBeenCalledTimes(1);
    });

    it('should be disabled when disabled prop is true', () => {
      render(<Button disabled>Disabled</Button>);
      expect(screen.getByRole('button')).toBeDisabled();
    });

    it('should not call onClick when disabled', () => {
      const handleClick = jest.fn();
      render(
        <Button disabled onClick={handleClick}>
          Disabled
        </Button>
      );

      fireEvent.click(screen.getByRole('button'));
      expect(handleClick).not.toHaveBeenCalled();
    });
  });

  describe('Custom className', () => {
    it('should merge custom className with base styles', () => {
      render(<Button className='custom-class'>Custom</Button>);
      const button = screen.getByRole('button');
      expect(button).toHaveClass('custom-class');
    });
  });

  describe('HTML button props passthrough', () => {
    it('should pass through type prop', () => {
      render(<Button type='submit'>Submit</Button>);
      expect(screen.getByRole('button')).toHaveAttribute('type', 'submit');
    });

    it('should pass through aria-label', () => {
      render(<Button aria-label='Custom label'>Label</Button>);
      expect(screen.getByLabelText('Custom label')).toBeInTheDocument();
    });
  });
});
