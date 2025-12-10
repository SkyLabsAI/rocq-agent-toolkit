import React from 'react';
import { render, screen, fireEvent } from '@testing-library/react';
import ThemeSwitcher from './ThemeSwitcher';
import { useTheme } from '@/contexts/ThemeContext';

// Mock the useTheme hook
jest.mock('@/contexts/ThemeContext', () => ({
  useTheme: jest.fn(),
}));

describe('ThemeSwitcher', () => {
  const mockToggleTheme = jest.fn();

  beforeEach(() => {
    mockToggleTheme.mockClear();
  });

  it('renders correctly in light mode', () => {
    (useTheme as jest.Mock).mockReturnValue({
      theme: 'light',
      toggleTheme: mockToggleTheme,
    });

    render(<ThemeSwitcher />);

    const button = screen.getByRole('button', { name: /switch to dark mode/i });
    expect(button).toBeInTheDocument();
    // Check for sun icon (light mode shows sun, button switches to dark)
    // Actually looking at code: theme === 'light' ? renders sun icon : renders moon icon
    // And aria-label is `Switch to ${theme === 'light' ? 'dark' : 'light'} mode`
  });

  it('renders correctly in dark mode', () => {
    (useTheme as jest.Mock).mockReturnValue({
      theme: 'dark',
      toggleTheme: mockToggleTheme,
    });

    render(<ThemeSwitcher />);

    const button = screen.getByRole('button', {
      name: /switch to light mode/i,
    });
    expect(button).toBeInTheDocument();
  });

  it('toggles theme when clicked', () => {
    (useTheme as jest.Mock).mockReturnValue({
      theme: 'light',
      toggleTheme: mockToggleTheme,
    });

    render(<ThemeSwitcher />);

    const button = screen.getByRole('button');
    fireEvent.click(button);

    expect(mockToggleTheme).toHaveBeenCalledTimes(1);
  });

  it('applies custom className', () => {
    (useTheme as jest.Mock).mockReturnValue({
      theme: 'light',
      toggleTheme: mockToggleTheme,
    });

    render(<ThemeSwitcher className='custom-class' />);

    const button = screen.getByRole('button');
    expect(button).toHaveClass('custom-class');
  });
});
