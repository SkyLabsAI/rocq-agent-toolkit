import React, { useEffect, useState } from 'react';
import { createPortal } from 'react-dom';

import { Button } from '@/components/base/ui/button';
import { ChevronUpIcon } from '@/icons/chevron-up';
import type { TaskOutput } from '@/types/types';

import { StatusBadge } from './base/statusBadge';
import Link from 'next/link';

interface TaskDetailsPanelProps {
  task: TaskOutput | null;
  isOpen: boolean;
  onClose: () => void;
  openCodeModal: (task: TaskOutput) => void;
}

const TaskDetailsPanel: React.FC<TaskDetailsPanelProps> = ({
  task,
  isOpen,
  onClose,
  openCodeModal,
}) => {
  const [expandedResults, setExpandedResults] = useState(false);
  const [mounted, setMounted] = useState(false);

  useEffect(() => {
    setMounted(true);
    return () => setMounted(false);
  }, []);

  const toggleResultExpansion = () => {
    setExpandedResults(prev => !prev);
  };

  if (!task || !mounted) return null;

  const panelContent = (
    <>
      {/* Backdrop */}
      <div
        className={`fixed inset-0 bg-black/50 z-40 transition-opacity duration-300 ${
          isOpen ? 'opacity-100' : 'opacity-0 pointer-events-none'
        }`}
        onClick={onClose}
      />

      {/* Slide-out Panel */}
      <div
        className={`fixed top-0 right-0 h-screen w-[600px] bg-elevation-surface border-l border-elevation-surface-overlay z-50 transform transition-transform duration-300 ease-in-out ${
          isOpen ? 'translate-x-0' : 'translate-x-full'
        } overflow-y-auto`}
      >
        {/* Header */}
        <div className='sticky top-0 bg-elevation-surface-raised border-b border-elevation-surface-overlay p-6 flex items-center justify-between z-10'>
          <h2 className='font-noto-sans font-semibold text-lg text-text'>
            Task Details
          </h2>
          <button
            onClick={onClose}
            className='p-2 hover:bg-elevation-surface-overlay rounded-lg transition-colors'
            title='Close'
          >
            <ChevronUpIcon className='-rotate-90 size-5' />
          </button>
        </div>

        {/* Content */}
        <div className='p-6 space-y-6'>
          {/* Task Info Section */}
          <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg p-5'>
            <div className='space-y-4'>
              <div className='flex flex-col gap-1.5'>
                <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                  Task ID
                </p>
                <p className='font-noto-sans font-normal text-sm text-text break-all'>
                  {task.task_id}
                </p>
              </div>

              <div className='flex flex-col gap-1.5'>
                <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                  Trace ID
                </p>
                <p className='font-noto-sans font-normal text-sm text-text break-all'>
                  {task.trace_id || 'Not found'}
                </p>
              </div>

              <div className='flex flex-col gap-1.5'>
                <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                  Task Kind
                </p>
                <p className='font-noto-sans font-normal text-sm text-text'>
                  {typeof task.task_kind === 'string'
                    ? task.task_kind
                    : task.task_kind?.kind || 'Not found'}
                </p>
              </div>

              <div className='flex flex-col gap-1.5'>
                <p className='font-noto-sans font-normal text-sm text-text-disabled'>
                  Status
                </p>
                <StatusBadge status={task.status} />
              </div>
            </div>
          </div>

          {/* Performance Metrics */}
          <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg p-5'>
            <p className='font-noto-sans font-semibold text-base text-text mb-4'>
              Performance Metrics
            </p>
            <div className='space-y-4'>
              <div className='grid grid-cols-2 gap-4'>
                <div className='flex flex-col gap-1.5'>
                  <p className='font-inter font-normal text-sm text-text-disabled'>
                    Execution Time
                  </p>
                  <p className='font-inter font-normal text-sm text-text'>
                    {`${task.metrics.resource_usage.execution_time_sec.toFixed(2)}s`}
                  </p>
                </div>

                <div className='flex flex-col gap-1.5'>
                  <p className='font-inter font-normal text-sm text-text-disabled'>
                    CPU Time
                  </p>
                  <p className='font-inter font-normal text-sm text-text'>
                    {task.metrics?.resource_usage?.cpu_time_sec.toFixed(2)}s
                  </p>
                </div>

                <div className='flex flex-col gap-1.5'>
                  <p className='font-inter font-normal text-sm text-text-disabled'>
                    GPU Time
                  </p>
                  <p className='font-inter font-normal text-sm text-text'>
                    {`${task.metrics.resource_usage.gpu_time_sec.toFixed(2)}s`}
                  </p>
                </div>

                <div className='flex flex-col gap-1.5'>
                  <p className='font-inter font-normal text-sm text-text-disabled'>
                    LLM Calls
                  </p>
                  <p className='font-inter font-normal text-sm text-text'>
                    {task.metrics?.llm_invocation_count || '_'}
                  </p>
                </div>
              </div>

              <div className='grid grid-cols-2 gap-4'>
                <div className='flex flex-col gap-1.5'>
                  <p className='font-inter font-normal text-sm text-text-disabled'>
                    Total Tokens
                  </p>
                  <p className='font-inter font-normal text-sm text-text'>
                    {task.metrics?.token_counts?.total_tokens?.toLocaleString() ||
                      '_'}
                  </p>
                </div>

                <div className='flex flex-col gap-1.5'>
                  <p className='font-inter font-normal text-sm text-text-disabled'>
                    Input Tokens
                  </p>
                  <p className='font-inter font-normal text-sm text-text'>
                    {task.metrics?.token_counts?.input_tokens?.toLocaleString() ||
                      '_'}
                  </p>
                </div>

                <div className='flex flex-col gap-1.5'>
                  <p className='font-inter font-normal text-sm text-text-disabled'>
                    Output Tokens
                  </p>
                  <p className='font-inter font-normal text-sm text-text'>
                    {task.metrics?.token_counts?.output_tokens?.toLocaleString() ||
                      '_'}
                  </p>
                </div>
              </div>
            </div>
          </div>

          {/* Custom Metrics */}
          {task.metrics?.custom &&
            Object.keys(task.metrics.custom).length > 0 && (
              <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg p-5'>
                <p className='font-noto-sans font-semibold text-base text-text mb-4'>
                  Custom Metrics
                </p>
                <div className='grid grid-cols-2 gap-4'>
                  {Object.entries(task.metrics.custom).map(([key, value]) => (
                    <div key={key} className='flex flex-col gap-1.5'>
                      <p className='font-inter font-normal text-sm text-text-disabled'>
                        {key}
                      </p>
                      <p className='font-inter font-normal text-sm text-text'>
                        {String(value)}
                      </p>
                    </div>
                  ))}
                </div>
              </div>
            )}

          {/* Task Result */}
          <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg p-5'>
            <button
              onClick={toggleResultExpansion}
              className='flex items-center gap-2 font-inter font-semibold text-base text-text hover:text-text-disabled transition-colors mb-4'
            >
              <ChevronUpIcon
                className={`size-4 transition-transform ${
                  expandedResults ? 'rotate-180' : ''
                }`}
              />
              Task Result
              {expandedResults ? ' (Full JSON)' : ''}
            </button>
            <div className='bg-elevation-surface-sunken rounded p-4 max-h-96 overflow-auto'>
              <pre className='font-inter font-normal text-sm text-text whitespace-pre-wrap'>
                {expandedResults
                  ? task.results
                    ? JSON.stringify(task.results, null, 2)
                    : 'No results available.'
                  : task.results?.side_effects?.doc_interaction
                    ? typeof task.results.side_effects.doc_interaction ===
                      'string'
                      ? task.results.side_effects.doc_interaction
                      : JSON.stringify(
                          task.results.side_effects.doc_interaction,
                          null,
                          2
                        )
                    : 'No doc interaction results available.'}
              </pre>
            </div>
          </div>

          {/* View Logs Button */}
          <Button
            variant='default'
            onClick={() => openCodeModal(task)}
            className='w-full'
          >
            View Logs
          </Button>

          <Link href={`/runs/${task.run_id}/tasks/${task.task_id}`}>
            <Button
              variant='default'
              onClick={() => openCodeModal(task)}
              className='w-full'
            >
              View Full
            </Button>
          </Link>
        </div>
      </div>
    </>
  );

  return createPortal(panelContent, document.body);
};

export default TaskDetailsPanel;
