import { useRouter } from 'next/navigation';
import React, { useState } from 'react';

import Button from '@/components/base/ui/button';
import Toast from '@/components/base/ui/toast';
import FileUpload from '@/components/file-upload';
import { uploadTasksYaml } from '@/services/dataservice';

import { useTaskSets } from '@/hooks/use-projects';

const TaskSetView: React.FC = () => {
  const { tasksets, loading, error } = useTaskSets();
  const router = useRouter();
  const [isUploadModalOpen, setIsUploadModalOpen] = useState(false);
  const [isUploading, setIsUploading] = useState(false);
  const [toastMessage, setToastMessage] = useState<string | null>(null);
  const [toastType, setToastType] = useState<'success' | 'error'>('success');

  const handleTaskSetClick = (tasksetId: string) => {
    router.push(`/taskset?id=${encodeURIComponent(tasksetId)}`);
  };

  const handleFileUpload = async (file: File) => {
    try {
      setIsUploading(true);
      const response = await uploadTasksYaml(file);

      if (response.success) {
        setToastType('success');
        setToastMessage(
          `Successfully uploaded ${file.name}. ${response.tasks_created} tasks created, ${response.tasks_updated} tasks updated.`
        );
        setIsUploadModalOpen(false);

        // Reload the page after 2 seconds to show new tasks
        setTimeout(() => {
          window.location.reload();
        }, 2000);
      } else {
        setToastType('error');
        setToastMessage(response.message || 'Upload failed');
      }
    } catch (err) {
      setToastType('error');
      setToastMessage(
        err instanceof Error
          ? `Upload failed: ${err.message}`
          : 'Failed to upload file'
      );
    } finally {
      setIsUploading(false);
    }
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
      <div
        className='p-8 text-center text-text-disabled'
        data-testid='tasksets-error'
      >
        {error}
      </div>
    );
  }

  return (
    <>
      <div data-testid='tasksets-view'>
        <div className='px-6 py-4 border-b border-elevation-surface-overlay bg-elevation-surface-raised flex items-center justify-between'>
          <div className='text-[16px] font-semibold text-text'>Projects</div>
          <Button
            onClick={() => setIsUploadModalOpen(true)}
            variant='default'
          >
            Upload Tasks
          </Button>
        </div>
        <table className='w-full text-left border-collapse'>
          <tbody className='divide-y divide-elevation-surface-overlay'>
          {tasksets.map(taskset => (
            <tr
              key={taskset.id}
              className='hover:bg-white/5 cursor-pointer transition-colors duration-200'
              onClick={() => handleTaskSetClick(taskset.id)}
              data-testid={`taskset-row-${taskset.id}`}
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

      {/* Upload Modal */}
      <FileUpload
        isOpen={isUploadModalOpen}
        onClose={() => {
          if (!isUploading) {
            setIsUploadModalOpen(false);
          }
        }}
        onFileSelect={handleFileUpload}
        disabled={isUploading}
        title='Upload Tasks from YAML'
      />

      {/* Toast Notification */}
      <Toast
        message={toastMessage || ''}
        type={toastType}
        isOpen={!!toastMessage}
        onClose={() => setToastMessage(null)}
        duration={3000}
      />
    </>
  );
};

// Legacy export for backward compatibility
const ProjectView = TaskSetView;
export default TaskSetView;
export { ProjectView };
