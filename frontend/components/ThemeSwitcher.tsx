'use client';

import React from 'react';
import { useTheme } from '@/contexts/ThemeContext';

interface ThemeSwitcherProps {
  className?: string;
}

const ThemeSwitcher: React.FC<ThemeSwitcherProps> = ({ className = '' }) => {
  const { theme, toggleTheme } = useTheme();

  return (
    <button
      onClick={toggleTheme}
      className={`
        relative inline-flex items-center justify-center
        w-12 h-6 rounded-full
        bg-background-neutral-bold
        hover:bg-background-neutral-bold-hovered
        active:bg-background-neutral-bold-pressed
        transition-all duration-200 ease-in-out
        focus:outline-none focus:ring-2 focus:ring-border-focused focus:ring-offset-2
        ${className}
      `}
      aria-label={`Switch to ${theme === 'light' ? 'dark' : 'light'} mode`}
      title={`Switch to ${theme === 'light' ? 'dark' : 'light'} mode`}
    >
      {/* Toggle knob */}
      <span
        className={`
          absolute top-0.5 w-5 h-5 rounded-full
          bg-elevation-surface
          shadow-sm
          transition-transform duration-200 ease-in-out
          flex items-center justify-center
          ${theme === 'dark' ? 'translate-x-6' : 'translate-x-0.5'}
        `}
      >
        {/* Sun icon (light mode) */}
        <svg
          className={`w-3 h-3 transition-opacity duration-200 ${
            theme === 'light' ? 'opacity-100' : 'opacity-0'
          } absolute`}
          fill="currentColor"
          viewBox="0 0 20 20"
        >
          <path
            fillRule="evenodd"
            d="M10 2a1 1 0 011 1v1a1 1 0 11-2 0V3a1 1 0 011-1zm4 8a4 4 0 11-8 0 4 4 0 018 0zm-.464 4.95l.707.707a1 1 0 001.414-1.414l-.707-.707a1 1 0 00-1.414 1.414zm2.12-10.607a1 1 0 010 1.414l-.706.707a1 1 0 11-1.414-1.414l.707-.707a1 1 0 011.414 0zM17 11a1 1 0 100-2h-1a1 1 0 100 2h1zm-7 4a1 1 0 011 1v1a1 1 0 11-2 0v-1a1 1 0 011-1zM5.05 6.464A1 1 0 106.465 5.05l-.708-.707a1 1 0 00-1.414 1.414l.707.707zm1.414 8.486l-.707.707a1 1 0 01-1.414-1.414l.707-.707a1 1 0 011.414 1.414zM4 11a1 1 0 100-2H3a1 1 0 000 2h1z"
            clipRule="evenodd"
          />
        </svg>

        {/* Moon icon (dark mode) */}
        <svg
          className={`w-3 h-3 transition-opacity duration-200 ${
            theme === 'dark' ? 'opacity-100' : 'opacity-0'
          } absolute`}
          fill="currentColor"
          viewBox="0 0 20 20"
        >
          <path d="M17.293 13.293A8 8 0 016.707 2.707a8.001 8.001 0 1010.586 10.586z" />
        </svg>
      </span>
    </button>
  );
};

export default ThemeSwitcher;