'use client';

import React, { useCallback, useState } from 'react';

import Modal from '@/components/base/ui/modal';

interface FileUploadProps {
  onFileSelect: (file: File) => void;
  accept?: string;
  disabled?: boolean;
  className?: string;
  isOpen?: boolean;
  onClose?: () => void;
  title?: string;
}

const FileUpload: React.FC<FileUploadProps> = ({
  onFileSelect,
  accept = '.yaml,.yml',
  disabled = false,
  className = '',
  isOpen,
  onClose,
  title = 'Upload Tasks from YAML',
}) => {
  const [isDragging, setIsDragging] = useState(false);
  const [fileName, setFileName] = useState<string | null>(null);

  const handleFileSelected = useCallback(
    (file: File) => {
      setFileName(file.name);
      onFileSelect(file);
    },
    [onFileSelect]
  );

  const handleDragEnter = useCallback(
    (e: React.DragEvent) => {
      e.preventDefault();
      e.stopPropagation();
      if (!disabled) {
        setIsDragging(true);
      }
    },
    [disabled]
  );

  const handleDragLeave = useCallback(
    (e: React.DragEvent) => {
      e.preventDefault();
      e.stopPropagation();
      setIsDragging(false);
    },
    []
  );

  const handleDragOver = useCallback((e: React.DragEvent) => {
    e.preventDefault();
    e.stopPropagation();
  }, []);

  const handleDrop = useCallback(
    (e: React.DragEvent) => {
      e.preventDefault();
      e.stopPropagation();
      setIsDragging(false);

      if (disabled) return;

      const files = Array.from(e.dataTransfer.files);
      const yamlFile = files.find(
        file =>
          file.name.endsWith('.yaml') || file.name.endsWith('.yml')
      );

      if (yamlFile) {
        handleFileSelected(yamlFile);
      }
    },
    [disabled, handleFileSelected]
  );

  const handleFileInput = useCallback(
    (e: React.ChangeEvent<HTMLInputElement>) => {
      const files = e.target.files;
      if (files && files.length > 0) {
        const file = files[0];
        handleFileSelected(file);
      }
    },
    [handleFileSelected]
  );

  const uploadContent = (
    <div className={`relative ${className}`}>
      <div
        className={`
          border-2 border-dashed rounded-lg p-6 transition-colors
          ${
            isDragging
              ? 'border-primary-default bg-primary-default/10'
              : 'border-elevation-surface-overlay bg-elevation-surface-sunken hover:border-elevation-surface-raised'
          }
          ${disabled ? 'opacity-50 cursor-not-allowed' : 'cursor-pointer'}
        `}
        onDragEnter={handleDragEnter}
        onDragOver={handleDragOver}
        onDragLeave={handleDragLeave}
        onDrop={handleDrop}
      >
        <input
          type='file'
          accept={accept}
          onChange={handleFileInput}
          disabled={disabled}
          className='hidden'
          id='file-upload-input'
        />
        <label
          htmlFor='file-upload-input'
          className={`flex flex-col items-center justify-center gap-3 ${
            disabled ? 'cursor-not-allowed' : 'cursor-pointer'
          }`}
        >
          <div className='text-center'>
            <svg
              className='mx-auto h-12 w-12 text-text-disabled'
              stroke='currentColor'
              fill='none'
              viewBox='0 0 48 48'
              aria-hidden='true'
            >
              <path
                d='M28 8H12a4 4 0 00-4 4v20m32-12v8m0 0v8a4 4 0 01-4 4H12a4 4 0 01-4-4v-4m32-4l-3.172-3.172a4 4 0 00-5.656 0L28 28M8 32l9.172-9.172a4 4 0 015.656 0L28 28m0 0l4 4m4-24h8m-4-4v8m-12 4h.02'
                strokeWidth={2}
                strokeLinecap='round'
                strokeLinejoin='round'
              />
            </svg>
            <div className='mt-4 flex text-sm leading-6 text-text'>
              <span className='relative cursor-pointer rounded-md font-semibold text-primary-default focus-within:outline-none focus-within:ring-2 focus-within:ring-primary-default focus-within:ring-offset-2 hover:text-primary-hovered'>
                {fileName ? `Selected: ${fileName}` : 'Click to upload'}
              </span>
              <p className='pl-1'>or drag and drop</p>
            </div>
            <p className='text-xs leading-5 text-text-disabled mt-2'>
              YAML files only (.yaml, .yml)
            </p>
          </div>
        </label>
      </div>
    </div>
  );

  // If modal props are provided, wrap in modal
  if (isOpen !== undefined && onClose) {
    return (
      <Modal isOpen={isOpen} onClose={onClose} title={title} size='default'>
        <div className='flex flex-col gap-4'>
          <div className='text-sm text-text-disabled'>
            Upload a YAML file containing task definitions. The file will be
            validated on the server.
          </div>
          {uploadContent}
        </div>
      </Modal>
    );
  }

  // Otherwise return just the upload component
  return uploadContent;
};

export default FileUpload;
