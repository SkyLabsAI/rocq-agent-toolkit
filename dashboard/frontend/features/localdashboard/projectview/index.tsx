import { useRouter } from 'next/navigation';
import React from 'react';

import { useTaskSets, useProjects } from '@/hooks/use-projects';

const TaskSetView: React.FC = () => {
  const { tasksets, loading, error } = useTaskSets();
  const router = useRouter();

  const handleTaskSetClick = (tasksetId: string) => {
    router.push(`/taskset/${tasksetId}`);
  };

  if (loading) {
    return (
      <div className='flex justify-center p-8' data-testid='tasksets-loading'>
        <div className='animate-spin rounded-full h-8 w-8 border-b-2 border-blue-400'></div>
      </div>
    );
  }

  if (error) {
    return (
      <div className='p-8 text-center text-text-disabled' data-testid='tasksets-error'>
        {error}
      </div>
    );
  }

  return (
    <div data-testid='tasksets-view'>
      <table className='w-full text-left border-collapse'>
        <tbody className='divide-y divide-elevation-surface-overlay'>
          <tr className='text-text' data-testid='tasksets-header-row'>
            <td>
              <div className='px-6 text-[16px] py-5 font-semibold'>
                TaskSets
              </div>
            </td>
          </tr>
          {tasksets.map(taskset => (
            <tr
              key={taskset.taskset_id}
              className='hover:bg-white/5 cursor-pointer transition-colors duration-200'
              onClick={() => handleTaskSetClick(taskset.taskset_id)}
              data-testid={`taskset-row-${taskset.taskset_id}`}
            >
              <td className='px-6 py-4 text-text font-medium'>
                <div className='flex items-center gap-3'>
                  <div className='h-6 w-6 bg-background-accent-gray-subtlest rounded-lg flex items-center justify-center'>
                    <span className='text-text font-semibold text-sm'>
                      {taskset.name.charAt(0).toUpperCase()}
                    </span>
                  </div>
                  <span className='text-[16px]' data-testid='taskset-name'>
                    {taskset.name}
                  </span>
                </div>
              </td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
};

// Legacy export for backward compatibility
const ProjectView = TaskSetView;
export default TaskSetView;
export { ProjectView };

