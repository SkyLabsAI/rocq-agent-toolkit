import { render, screen } from '@testing-library/react';
import React from 'react';

import { Button } from './index';

describe('Button', () => {
  it('should render button with children', () => {
    render(<Button>Click Me</Button>);
    expect(screen.getByText('Click Me')).toBeInTheDocument();
  });

  it('should apply default variant styles', () => {
    render(<Button variant='default'>Default</Button>);
    const button = screen.getByText('Default');
    expect(button).toBeInTheDocument();
  });

  it('should apply danger variant styles', () => {
    render(<Button variant='danger'>Danger</Button>);
    const button = screen.getByText('Danger');
    expect(button).toBeInTheDocument();
  });

  it('should apply ghost variant styles', () => {
    render(<Button variant='ghost'>Ghost</Button>);
    const button = screen.getByText('Ghost');
    expect(button).toBeInTheDocument();
  });

  it('should apply outline variant styles', () => {
    render(<Button variant='outline'>Outline</Button>);
    const button = screen.getByText('Outline');
    expect(button).toBeInTheDocument();
  });

  it('should render left icon', () => {
    render(
      <Button leftIcon={<span data-testid='left-icon'>→</span>}>
        With Left Icon
      </Button>
    );
    expect(screen.getByTestId('left-icon')).toBeInTheDocument();
  });

  it('should render right icon', () => {
    render(
      <Button rightIcon={<span data-testid='right-icon'>←</span>}>
        With Right Icon
      </Button>
    );
    expect(screen.getByTestId('right-icon')).toBeInTheDocument();
  });

  it('should handle click events', () => {
    const handleClick = jest.fn();
    render(<Button onClick={handleClick}>Click</Button>);

    screen.getByText('Click').click();
    expect(handleClick).toHaveBeenCalledTimes(1);
  });

  it('should be disabled when disabled prop is true', () => {
    render(<Button disabled>Disabled</Button>);
    const button = screen.getByRole('button', { name: 'Disabled' });
    expect(button).toBeDisabled();
  });

  it('should apply custom className', () => {
    render(<Button className='custom-class'>Custom</Button>);
    const button = screen.getByRole('button', { name: 'Custom' });
    expect(button).toHaveClass('custom-class');
  });
});
