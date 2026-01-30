'use client';

import React, { useState, useCallback } from 'react';

import Button from '@/components/base/ui/button';
import Modal from '@/components/base/ui/modal';
import { bulkAddTags } from '@/services/dataservice';

interface AddTagModalProps {
  isOpen: boolean;
  onClose: () => void;
  taskId: number;
  taskName: string;
  onSuccess?: () => void;
}

const AddTagModal: React.FC<AddTagModalProps> = ({
  isOpen,
  onClose,
  taskId,
  taskName,
  onSuccess,
}) => {
  const [tagInput, setTagInput] = useState('');
  const [isAddingTag, setIsAddingTag] = useState(false);
  const [errorMessage, setErrorMessage] = useState<string | null>(null);

  const handleAddTag = useCallback(async () => {
    if (!tagInput.trim() || taskId === -1) return;

    try {
      setIsAddingTag(true);
      setErrorMessage(null);

      // Parse tags (comma-separated or space-separated)
      const tags = tagInput
        .split(/[,\s]+/)
        .map(t => t.trim())
        .filter(t => t.length > 0);

      if (tags.length === 0) {
        setErrorMessage('Please enter at least one tag');
        setIsAddingTag(false);
        return;
      }

      await bulkAddTags({
        task_ids: [taskId],
        tags: tags,
      });

      // Success - reset and close
      setTagInput('');
      setIsAddingTag(false);
      onSuccess?.();
      onClose();
    } catch (err) {
      setErrorMessage(
        err instanceof Error ? err.message : 'Failed to add tags'
      );
      setIsAddingTag(false);
    }
  }, [tagInput, taskId, onClose, onSuccess]);

  const handleClose = useCallback(() => {
    if (!isAddingTag) {
      setTagInput('');
      setErrorMessage(null);
      onClose();
    }
  }, [isAddingTag, onClose]);

  const handleKeyDown = useCallback(
    (e: React.KeyboardEvent<HTMLInputElement>) => {
      if (e.key === 'Enter' && !isAddingTag && tagInput.trim()) {
        handleAddTag();
      }
    },
    [isAddingTag, tagInput, handleAddTag]
  );

  return (
    <Modal
      isOpen={isOpen}
      onClose={handleClose}
      title={`Add Tags to Task: ${taskName}`}
      size='default'
    >
      <div className='flex flex-col gap-4'>
        <div>
          <label
            htmlFor='tag-input'
            className='block text-sm font-semibold text-text mb-2'
          >
            Tags <span className='text-text-danger'>*</span>
          </label>
          <input
            id='tag-input'
            type='text'
            value={tagInput}
            onChange={e => setTagInput(e.target.value)}
            placeholder='Enter tags (comma or space separated)'
            className='w-full px-3 py-2 bg-elevation-surface border border-elevation-surface-overlay rounded text-sm text-text placeholder-text-disabled focus:outline-none focus:ring-2 focus:ring-border-focused'
            disabled={isAddingTag}
            onKeyDown={handleKeyDown}
          />
          <p className='text-xs text-text-disabled mt-1'>
            Separate multiple tags with commas or spaces
          </p>
          {errorMessage && (
            <p className='text-xs text-text-danger mt-1'>{errorMessage}</p>
          )}
        </div>

        <div className='flex gap-3 justify-end pt-2'>
          <Button variant='ghost' onClick={handleClose} disabled={isAddingTag}>
            Cancel
          </Button>
          <Button
            variant='default'
            onClick={handleAddTag}
            disabled={isAddingTag || !tagInput.trim()}
          >
            {isAddingTag ? 'Adding...' : 'Add Tags'}
          </Button>
        </div>
      </div>
    </Modal>
  );
};

export default AddTagModal;
