'use client';

import React, { useEffect } from 'react';
import { createPortal } from 'react-dom';

interface ToastProps {
  message: string;
  type?: 'success' | 'error';
  isOpen: boolean;
  onClose: () => void;
  duration?: number; // Auto-close duration in milliseconds, 0 means no auto-close
}

const Toast: React.FC<ToastProps> = ({
  message,
  type = 'success',
  isOpen,
  onClose,
  duration = 3000,
}) => {
  // Auto-close after duration
  useEffect(() => {
    if (isOpen && duration > 0) {
      const timer = setTimeout(() => {
        onClose();
      }, duration);

      return () => {
        clearTimeout(timer);
      };
    }
  }, [isOpen, duration, onClose]);

  if (!isOpen || typeof window === 'undefined') {
    return null;
  }

  const toastContent = (
    <div className='fixed bottom-4 right-4 z-[9999] px-4 py-3 bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg shadow-lg flex items-center gap-3 min-w-[300px] max-w-[500px] animate-in slide-in-from-bottom-2'>
      <div className='flex-1'>
        <p
          className={`text-sm ${
            type === 'success' ? 'text-text-success' : 'text-text-danger'
          }`}
        >
          {message}
        </p>
      </div>
      <button
        onClick={onClose}
        className='text-text-disabled hover:text-text transition-colors text-lg leading-none'
        aria-label='Close notification'
      >
        ×
      </button>
    </div>
  );

  // Use portal to mount toast at the root of the DOM
  return createPortal(toastContent, document.body);
};

export default Toast;
