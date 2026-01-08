import React, { useEffect, useMemo, useState } from 'react';

import type { TaskOutput } from '@/types/types';

import { StatusBadge } from './base/statusBadge';
import { TagsDisplay } from './tags-display';

interface TasksTableProps {
  tasks: TaskOutput[];
  onTaskClick: (task: TaskOutput) => void;
  initialSelectedTags?: string[];
  onTagsChange?: (tags: string[]) => void;
  initialStatusFilter?: 'all' | 'Success' | 'Failure';
  onStatusChange?: (status: 'all' | 'Success' | 'Failure') => void;
  initialTaskIdFilter?: string;
  onTaskIdChange?: (taskId: string) => void;
}

const TasksTable: React.FC<TasksTableProps> = ({
  tasks,
  onTaskClick,
  initialSelectedTags = [],
  onTagsChange,
  initialStatusFilter = 'all',
  onStatusChange,
  initialTaskIdFilter = '',
  onTaskIdChange,
}) => {
  const [taskIdFilter, setTaskIdFilter] = useState(initialTaskIdFilter);
  const [statusFilter, setStatusFilter] = useState<
    'all' | 'Success' | 'Failure'
  >(initialStatusFilter);
  const [selectedTags, setSelectedTags] =
    useState<string[]>(initialSelectedTags);
  const [tagSearchInput, setTagSearchInput] = useState('');

  // Notify parent component when tags change
  useEffect(() => {
    if (onTagsChange) {
      onTagsChange(selectedTags);
    }
  }, [selectedTags, onTagsChange]);

  // Notify parent component when status changes
  useEffect(() => {
    if (onStatusChange) {
      onStatusChange(statusFilter);
    }
  }, [statusFilter, onStatusChange]);

  // Notify parent component when task ID filter changes
  useEffect(() => {
    if (onTaskIdChange) {
      onTaskIdChange(taskIdFilter);
    }
  }, [taskIdFilter, onTaskIdChange]);

  // Extract all unique tags from tasks
  const availableTags = useMemo(() => {
    const tagsSet = new Set<string>();
    tasks.forEach(task => {
      const tags = task.metadata?.tags;
      if (tags && typeof tags === 'object') {
        Object.entries(tags).forEach(([key, value]) => {
          // Convert all values to strings to handle numbers, booleans, etc.
          if (value != null) {
            // Skip null and undefined
            const stringValue = String(value);
            tagsSet.add(`${key}:${stringValue}`);
          }
        });
      }
    });
    return Array.from(tagsSet).sort();
  }, [tasks]);

  // Filter available tags based on search input
  const filteredAvailableTags = useMemo(() => {
    if (!tagSearchInput) return availableTags;
    return availableTags.filter(tag =>
      tag.toLowerCase().includes(tagSearchInput.toLowerCase())
    );
  }, [availableTags, tagSearchInput]);

  // Toggle tag selection
  const toggleTag = (tag: string) => {
    setSelectedTags(prev =>
      prev.includes(tag) ? prev.filter(t => t !== tag) : [...prev, tag]
    );
  };

  // Clear all selected tags
  const clearAllTags = () => {
    setSelectedTags([]);
  };

  // Filter tasks based on current filters
  const filteredTasks = useMemo(() => {
    return tasks.filter(task => {
      const matchesTaskId = task.task_name
        .toLowerCase()
        .includes(taskIdFilter.toLowerCase());
      const matchesStatus =
        statusFilter === 'all' || task.status === statusFilter;

      // Check if task matches selected tags (ALL selected tags must match)
      let matchesTags = true;
      if (selectedTags.length > 0) {
        const taskTags = task.metadata?.tags;
        if (!taskTags || typeof taskTags !== 'object') {
          matchesTags = false;
        } else {
          matchesTags = selectedTags.every(selectedTag => {
            const [key, value] = selectedTag.split(':');
            // Convert task tag value to string for comparison
            const taskTagValue = taskTags[key];
            return taskTagValue != null && String(taskTagValue) === value;
          });
        }
      }

      return matchesTaskId && matchesStatus && matchesTags;
    });
  }, [tasks, taskIdFilter, statusFilter, selectedTags]);

  return (
    <div className='space-y-4'>
      {/* Filters Section */}
      <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg p-4'>
        <div className='grid grid-cols-2 gap-4'>
          {/* Task ID Filter */}
          <div className='flex flex-col gap-2'>
            <label
              htmlFor='task-id-filter'
              className='font-noto-sans text-sm text-text-disabled'
            >
              Filter by Task ID
            </label>
            <input
              id='task-id-filter'
              type='text'
              value={taskIdFilter}
              onChange={e => setTaskIdFilter(e.target.value)}
              placeholder='Search task ID...'
              className='px-3 py-2 bg-elevation-surface border border-elevation-surface-overlay rounded text-sm text-text placeholder-text-disabled focus:outline-none focus:ring-2 focus:ring-text-information'
            />
          </div>

          {/* Status Filter */}
          <div className='flex flex-col gap-2'>
            <label
              htmlFor='status-filter'
              className='font-noto-sans text-sm text-text-disabled'
            >
              Filter by Status
            </label>
            <select
              id='status-filter'
              value={statusFilter}
              onChange={e =>
                setStatusFilter(e.target.value as 'all' | 'Success' | 'Failure')
              }
              className='px-3 py-2 bg-elevation-surface border border-elevation-surface-overlay rounded text-sm text-text focus:outline-none focus:ring-2 focus:ring-text-information'
            >
              <option value='all'>All Statuses</option>
              <option value='Success'>Success</option>
              <option value='Failure'>Failure</option>
            </select>
          </div>
        </div>

        {/* Tags Filter Section */}
        <div className='mt-4 pt-4 border-t border-elevation-surface-overlay'>
          <div className='flex items-center justify-between mb-2'>
            <label
              htmlFor='tag-search'
              className='font-noto-sans text-sm text-text-disabled'
            >
              Filter by Tags{' '}
              {selectedTags.length > 0 && `(${selectedTags.length} selected)`}
            </label>
            {selectedTags.length > 0 && (
              <button
                onClick={clearAllTags}
                className='px-2 py-1 text-xs text-text-information hover:text-text-information-hovered transition-colors'
              >
                Clear all
              </button>
            )}
          </div>

          {/* Tag Search Input */}
          <input
            id='tag-search'
            type='text'
            value={tagSearchInput}
            onChange={e => setTagSearchInput(e.target.value)}
            placeholder='Search tags...'
            className='w-full px-3 py-2 bg-elevation-surface border border-elevation-surface-overlay rounded text-sm text-text placeholder-text-disabled focus:outline-none focus:ring-2 focus:ring-text-information mb-2'
          />

          {/* Selected Tags */}
          {selectedTags.length > 0 && (
            <div className='mb-3 flex flex-wrap gap-2'>
              {selectedTags.map(tag => (
                <button
                  key={tag}
                  onClick={() => toggleTag(tag)}
                  className='px-3 py-1.5 bg-text-information text-elevation-surface rounded-full text-xs font-noto-sans flex items-center gap-2 hover:bg-text-information-hovered transition-colors'
                >
                  {tag}
                  <span className='text-xs'>×</span>
                </button>
              ))}
            </div>
          )}

          {/* Available Tags */}
          <div className='max-h-48 overflow-y-auto bg-elevation-surface border border-elevation-surface-overlay rounded p-2'>
            <div
              className='flex flex-wrap gap-2'
              role='group'
              aria-label='Available tags'
            >
              {filteredAvailableTags.length === 0 ? (
                <p className='text-xs text-text-disabled w-full text-center py-2'>
                  No tags available
                </p>
              ) : (
                filteredAvailableTags.map(tag => {
                  const isSelected = selectedTags.includes(tag);
                  return (
                    <button
                      key={tag}
                      onClick={() => toggleTag(tag)}
                      className={`px-3 py-1.5 rounded-full text-xs font-noto-sans transition-colors ${
                        isSelected
                          ? 'bg-text-information text-elevation-surface'
                          : 'bg-elevation-surface-overlay text-text hover:bg-elevation-surface-sunken'
                      }`}
                    >
                      {tag}
                    </button>
                  );
                })
              )}
            </div>
          </div>
        </div>

        {/* Results Count */}
        <div className='mt-3 pt-3 border-t border-elevation-surface-overlay'>
          <p className='font-noto-sans text-sm text-text-disabled'>
            Showing {filteredTasks.length} of {tasks.length} tasks
          </p>
        </div>
      </div>

      {/* Table Section */}
      <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg overflow-hidden'>
        <div className='overflow-x-auto'>
          <table className='w-full'>
            <thead className='bg-elevation-surface-sunken border-b border-elevation-surface-overlay'>
              <tr>
                <th className='px-6 py-3 text-left font-noto-sans font-semibold text-sm text-text-disabled'>
                  Task Name
                </th>
                <th className='px-6 py-3 text-left font-noto-sans font-semibold text-sm text-text-disabled'>
                  Status
                </th>
                <th className='px-6 py-3 text-left font-noto-sans font-semibold text-sm text-text-disabled'>
                  Tags
                </th>
              </tr>
            </thead>
            <tbody className='divide-y divide-elevation-surface-overlay'>
              {filteredTasks.length === 0 ? (
                <tr>
                  <td colSpan={3} className='px-6 py-8 text-center'>
                    <p className='font-noto-sans text-sm text-text-disabled'>
                      No tasks found matching your filters
                    </p>
                  </td>
                </tr>
              ) : (
                filteredTasks.map((task, _index) => {
                  const taskTags = task.metadata?.tags || {};

                  console.log(task.task_id, task.task_name);
                  return (
                    <tr
                      key={task.task_id}
                      onClick={() => onTaskClick(task)}
                      className='hover:bg-elevation-surface-overlay cursor-pointer transition-colors'
                    >
                      <td className='px-6 py-4 font-noto-sans text-sm text-text truncate max-w-xs'>
                        {task.task_name}
                      </td>
                      <td className='px-6 py-4'>
                        <StatusBadge status={task.status} />
                      </td>
                      <td className='px-6 py-4'>
                        {Object.keys(taskTags).length > 0 ? (
                          <TagsDisplay
                            tags={taskTags}
                            maxVisible={2}
                            modalTitle={`Tags for ${task.task_name}`}
                          />
                        ) : (
                          <span className='text-xs text-text-disabled'>
                            No tags
                          </span>
                        )}
                      </td>
                    </tr>
                  );
                })
              )}
            </tbody>
          </table>
        </div>
      </div>
    </div>
  );
};

export default TasksTable;
