import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';

import { ThemeProvider, useTheme } from '@/contexts/ThemeContext';

import ThemeSwitcher from './theme-switcher';

// Mock the ThemeContext
const mockToggleTheme = jest.fn();
const mockUseTheme = jest.fn();

jest.mock('@/contexts/theme-context', () => ({
  useTheme: () => mockUseTheme(),
}));

describe('ThemeSwitcher component', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  describe('Rendering', () => {
    it('should render as a button', () => {
      mockUseTheme.mockReturnValue({
        theme: 'light',
        toggleTheme: mockToggleTheme,
      });

      render(<ThemeSwitcher />);
      expect(screen.getByRole('button')).toBeInTheDocument();
    });

    it('should have correct aria-label for light mode', () => {
      mockUseTheme.mockReturnValue({
        theme: 'light',
        toggleTheme: mockToggleTheme,
      });

      render(<ThemeSwitcher />);
      expect(screen.getByLabelText('Switch to dark mode')).toBeInTheDocument();
    });

    it('should have correct aria-label for dark mode', () => {
      mockUseTheme.mockReturnValue({
        theme: 'dark',
        toggleTheme: mockToggleTheme,
      });

      render(<ThemeSwitcher />);
      expect(screen.getByLabelText('Switch to light mode')).toBeInTheDocument();
    });
  });

  describe('Icon display', () => {
    it('should render sun icon in light mode', () => {
      mockUseTheme.mockReturnValue({
        theme: 'light',
        toggleTheme: mockToggleTheme,
      });

      const { container } = render(<ThemeSwitcher />);
      const svg = container.querySelector('svg');
      expect(svg).toBeInTheDocument();
      // Sun icon has multiple path segments
      expect(
        container.querySelector('path[fill-rule="evenodd"]')
      ).toBeInTheDocument();
    });

    it('should render moon icon in dark mode', () => {
      mockUseTheme.mockReturnValue({
        theme: 'dark',
        toggleTheme: mockToggleTheme,
      });

      const { container } = render(<ThemeSwitcher />);
      const svg = container.querySelector('svg');
      expect(svg).toBeInTheDocument();
      // Moon icon has a simpler path
      expect(
        container.querySelector('path:not([fill-rule])')
      ).toBeInTheDocument();
    });
  });

  describe('Interactions', () => {
    it('should call toggleTheme when clicked', () => {
      mockUseTheme.mockReturnValue({
        theme: 'light',
        toggleTheme: mockToggleTheme,
      });

      render(<ThemeSwitcher />);
      fireEvent.click(screen.getByRole('button'));
      expect(mockToggleTheme).toHaveBeenCalledTimes(1);
    });
  });

  describe('Custom className', () => {
    it('should apply custom className', () => {
      mockUseTheme.mockReturnValue({
        theme: 'light',
        toggleTheme: mockToggleTheme,
      });

      render(<ThemeSwitcher className='custom-class' />);
      expect(screen.getByRole('button')).toHaveClass('custom-class');
    });

    it('should merge with existing classes', () => {
      mockUseTheme.mockReturnValue({
        theme: 'light',
        toggleTheme: mockToggleTheme,
      });

      render(<ThemeSwitcher className='custom-class' />);
      const button = screen.getByRole('button');
      expect(button).toHaveClass('custom-class');
      expect(button).toHaveClass('rounded');
    });
  });

  describe('Title attribute', () => {
    it('should have correct title for light mode', () => {
      mockUseTheme.mockReturnValue({
        theme: 'light',
        toggleTheme: mockToggleTheme,
      });

      render(<ThemeSwitcher />);
      expect(screen.getByTitle('Switch to dark mode')).toBeInTheDocument();
    });

    it('should have correct title for dark mode', () => {
      mockUseTheme.mockReturnValue({
        theme: 'dark',
        toggleTheme: mockToggleTheme,
      });

      render(<ThemeSwitcher />);
      expect(screen.getByTitle('Switch to light mode')).toBeInTheDocument();
    });
  });
});
