'use client';

import React, { useEffect, useState } from 'react';

import CodeViewer from '@/components/base/codeViewer';
import Modal from '@/components/base/ui/modal';
import { TagsDisplay } from '@/components/tags-display';
import { getTaskDetailsById } from '@/services/dataservice';
import type { TaskDetailsResponse } from '@/types/types';

interface TaskInfoModalProps {
  isOpen: boolean;
  onClose: () => void;
  taskId: number;
  taskName: string;
}

const TaskInfoModal: React.FC<TaskInfoModalProps> = ({
  isOpen,
  onClose,
  taskId,
  taskName,
}) => {
  const [task, setTask] = useState<TaskDetailsResponse | null>(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    if (isOpen && taskId) {
      const fetchTaskDetails = async () => {
        setLoading(true);
        setError(null);
        try {
          const taskDetails = await getTaskDetailsById(taskId);
          setTask(taskDetails);
        } catch (err) {
          setError(
            err instanceof Error ? err.message : 'Failed to fetch task details'
          );
        } finally {
          setLoading(false);
        }
      };

      fetchTaskDetails();
    } else {
      // Reset state when modal closes
      setTask(null);
      setError(null);
    }
  }, [isOpen, taskId]);

  return (
    <Modal
      isOpen={isOpen}
      onClose={onClose}
      title={`Task: ${taskName}`}
      size='large'
    >
      <div className='flex flex-col gap-6'>
        {loading ? (
          <div className='flex items-center justify-center gap-2 py-12'>
            <div className='animate-spin rounded-full h-8 w-8 border-b-2 border-elevation-surface-overlay'></div>
            <p className='font-noto-sans font-normal text-sm text-text-disabled'>
              Loading task details...
            </p>
          </div>
        ) : error ? (
          <div className='text-center py-12'>
            <p className='font-noto-sans font-normal text-sm text-text-danger'>
              {error}
            </p>
          </div>
        ) : task ? (
          <>
            {/* Task Information */}
            <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg p-5'>
              <p className='font-noto-sans font-semibold text-base text-text mb-4'>
                Task Information
              </p>
              <div className='grid grid-cols-2 gap-4'>
                <div className='flex flex-col gap-1.5'>
                  <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                    Task ID
                  </p>
                  <p className='font-noto-sans font-normal text-base text-text wrap-break-word'>
                    {task.task_id}
                  </p>
                </div>
                <div className='flex flex-col gap-1.5'>
                  <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                    Task Name
                  </p>
                  <p className='font-noto-sans font-normal text-base text-text wrap-break-word'>
                    {task.task_name}
                  </p>
                </div>
                <div className='flex flex-col gap-1.5'>
                  <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                    Task Kind
                  </p>
                  <p className='font-noto-sans font-normal text-base text-text wrap-break-word'>
                    {task.task_kind}
                  </p>
                </div>
                <div className='flex flex-col gap-1.5'>
                  <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                    Dataset ID
                  </p>
                  <p className='font-noto-sans font-normal text-base text-text wrap-break-word'>
                    {task.dataset_id}
                  </p>
                </div>
              </div>
            </div>

            {/* Dataset Information */}
            {task.dataset && (
              <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg p-5'>
                <p className='font-noto-sans font-semibold text-base text-text mb-4'>
                  Dataset Information
                </p>
                <div className='flex flex-col gap-3'>
                  <div className='flex flex-col gap-1.5'>
                    <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                      Dataset ID
                    </p>
                    <p className='font-noto-sans font-normal text-base text-text wrap-break-word'>
                      {task.dataset.dataset_id}
                    </p>
                  </div>
                  {task.dataset.description && (
                    <div className='flex flex-col gap-1.5'>
                      <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                        Description
                      </p>
                      <p className='font-noto-sans font-normal text-base text-text wrap-break-word'>
                        {task.dataset.description}
                      </p>
                    </div>
                  )}
                  <div className='flex flex-col gap-1.5'>
                    <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                      Created At
                    </p>
                    <p className='font-noto-sans font-normal text-base text-text wrap-break-word'>
                      {new Date(task.dataset.created_at).toLocaleString()}
                    </p>
                  </div>
                </div>
              </div>
            )}

            {/* Tags */}
            {task.tags && Object.keys(task.tags).length > 0 && (
              <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg p-5'>
                <p className='font-noto-sans font-semibold text-base text-text mb-4'>
                  Tags
                </p>
                <TagsDisplay
                  tags={task.tags}
                  maxVisible={10}
                  modalTitle={`Tags for ${task.task_name}`}
                />
              </div>
            )}
          </>
        ) : null}

        {/* Ground Truth */}
        {task && (
          <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg p-5'>
            <p className='font-noto-sans font-semibold text-base text-text mb-4'>
              Ground Truth
            </p>
            {task.ground_truth ? (
              <CodeViewer
                code={task.ground_truth}
                language='text'
                filename='ground_truth.txt'
              />
            ) : (
              <div className='text-center py-8'>
                <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                  No ground truth available
                </p>
              </div>
            )}
          </div>
        )}
      </div>
    </Modal>
  );
};

export default TaskInfoModal;
