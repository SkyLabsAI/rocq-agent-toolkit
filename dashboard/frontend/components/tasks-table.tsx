import React, { useState, useMemo } from 'react';
import { StatusBadge } from './base/statusBadge';
import type { TaskOutput } from '@/types/types';

interface TasksTableProps {
  tasks: TaskOutput[];
  onTaskClick: (task: TaskOutput) => void;
}

const TasksTable: React.FC<TasksTableProps> = ({ tasks, onTaskClick }) => {
  const [taskIdFilter, setTaskIdFilter] = useState('');
  const [statusFilter, setStatusFilter] = useState<'all' | 'Success' | 'Failure'>('all');

  // Filter tasks based on current filters
  const filteredTasks = useMemo(() => {
    return tasks.filter(task => {
      const matchesTaskId = task.task_id
        .toLowerCase()
        .includes(taskIdFilter.toLowerCase());
      const matchesStatus = statusFilter === 'all' || task.status === statusFilter;

      return matchesTaskId && matchesStatus;
    });
  }, [tasks, taskIdFilter, statusFilter]);

  return (
    <div className='space-y-4'>
      {/* Filters Section */}
      <div className='bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg p-4'>
        <div className='grid grid-cols-2 gap-4'>
          {/* Task ID Filter */}
          <div className='flex flex-col gap-2'>
            <label className='font-noto-sans text-sm text-text-disabled'>
              Filter by Task ID
            </label>
            <input
              type='text'
              value={taskIdFilter}
              onChange={e => setTaskIdFilter(e.target.value)}
              placeholder='Search task ID...'
              className='px-3 py-2 bg-elevation-surface border border-elevation-surface-overlay rounded text-sm text-text placeholder-text-disabled focus:outline-none focus:ring-2 focus:ring-text-information'
            />
          </div>

          {/* Status Filter */}
          <div className='flex flex-col gap-2'>
            <label className='font-noto-sans text-sm text-text-disabled'>
              Filter by Status
            </label>
            <select
              value={statusFilter}
              onChange={e => setStatusFilter(e.target.value as 'all' | 'Success' | 'Failure')}
              className='px-3 py-2 bg-elevation-surface border border-elevation-surface-overlay rounded text-sm text-text focus:outline-none focus:ring-2 focus:ring-text-information'
            >
              <option value='all'>All Statuses</option>
              <option value='Success'>Success</option>
              <option value='Failure'>Failure</option>
            </select>
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
                  Task ID
                </th>
                <th className='px-6 py-3 text-left font-noto-sans font-semibold text-sm text-text-disabled'>
                  Status
                </th>
              </tr>
            </thead>
            <tbody className='divide-y divide-elevation-surface-overlay'>
              {filteredTasks.length === 0 ? (
                <tr>
                  <td colSpan={2} className='px-6 py-8 text-center'>
                    <p className='font-noto-sans text-sm text-text-disabled'>
                      No tasks found matching your filters
                    </p>
                  </td>
                </tr>
              ) : (
                filteredTasks.map((task, index) => (
                  <tr
                    key={task.task_id + index}
                    onClick={() => onTaskClick(task)}
                    className='hover:bg-elevation-surface-overlay cursor-pointer transition-colors'
                  >
                    <td className='px-6 py-4 font-noto-sans text-sm text-text truncate max-w-xs'>
                      {task.task_id}
                    </td>
                    <td className='px-6 py-4'>
                      <StatusBadge status={task.status} />
                    </td>
                  </tr>
                ))
              )}
            </tbody>
          </table>
        </div>
      </div>
    </div>
  );
};

export default TasksTable;

