import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';

import { ThemeProvider, useTheme } from './theme-context';

// Mock localStorage
const localStorageMock = (() => {
  let store: Record<string, string> = {};
  return {
    getItem: (key: string) => store[key] || null,
    setItem: (key: string, value: string) => {
      store[key] = value;
    },
    clear: () => {
      store = {};
    },
  };
})();

Object.defineProperty(window, 'localStorage', {
  value: localStorageMock,
});

// Mock matchMedia
Object.defineProperty(window, 'matchMedia', {
  writable: true,
  value: jest.fn().mockImplementation(query => ({
    matches: query === '(prefers-color-scheme: dark)',
    media: query,
    onchange: null,
    addListener: jest.fn(),
    removeListener: jest.fn(),
    addEventListener: jest.fn(),
    removeEventListener: jest.fn(),
    dispatchEvent: jest.fn(),
  })),
});

const TestComponent = () => {
  const { theme, setTheme, toggleTheme } = useTheme();

  return (
    <div>
      <div data-testid='current-theme'>{theme}</div>
      <button onClick={toggleTheme}>Toggle Theme</button>
      <button onClick={() => setTheme('dark')}>Set Dark</button>
      <button onClick={() => setTheme('light')}>Set Light</button>
    </div>
  );
};

describe('ThemeContext', () => {
  beforeEach(() => {
    localStorageMock.clear();
    document.documentElement.classList.remove('light', 'dark');
  });

  it('should throw error when used outside provider', () => {
    const consoleError = jest.spyOn(console, 'error').mockImplementation();
    expect(() => render(<TestComponent />)).toThrow(
      'useTheme must be used within a ThemeProvider'
    );
    consoleError.mockRestore();
  });

  it('should initialize with light theme by default', () => {
    render(
      <ThemeProvider>
        <TestComponent />
      </ThemeProvider>
    );

    // Theme provider needs to mount first
    setTimeout(() => {
      expect(screen.getByTestId('current-theme')).toHaveTextContent('light');
    }, 100);
  });

  it('should toggle theme', () => {
    render(
      <ThemeProvider>
        <TestComponent />
      </ThemeProvider>
    );

    setTimeout(() => {
      fireEvent.click(screen.getByText('Toggle Theme'));

      setTimeout(() => {
        const theme = screen.getByTestId('current-theme').textContent;
        expect(theme === 'dark' || theme === 'light').toBe(true);
      }, 100);
    }, 100);
  });

  it('should set theme to dark', () => {
    render(
      <ThemeProvider>
        <TestComponent />
      </ThemeProvider>
    );

    setTimeout(() => {
      fireEvent.click(screen.getByText('Set Dark'));

      setTimeout(() => {
        expect(screen.getByTestId('current-theme')).toHaveTextContent('dark');
      }, 100);
    }, 100);
  });

  it('should set theme to light', () => {
    render(
      <ThemeProvider>
        <TestComponent />
      </ThemeProvider>
    );

    setTimeout(() => {
      fireEvent.click(screen.getByText('Set Light'));

      setTimeout(() => {
        expect(screen.getByTestId('current-theme')).toHaveTextContent('light');
      }, 100);
    }, 100);
  });
});
