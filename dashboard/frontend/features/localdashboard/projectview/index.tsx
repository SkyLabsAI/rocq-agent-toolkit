import { useRouter } from 'next/navigation';
import React, { useState } from 'react';

import Button from '@/components/base/ui/button';
import FileUpload from '@/components/file-upload';
import { uploadTasksYaml } from '@/services/dataservice';

import { useTaskSets } from '@/hooks/use-projects';

const TaskSetView: React.FC = () => {
  const { tasksets, loading, error } = useTaskSets();
  const router = useRouter();
  const [isUploadModalOpen, setIsUploadModalOpen] = useState(false);
  const [isUploading, setIsUploading] = useState(false);
  const [toastMessage, setToastMessage] = useState<string | null>(null);

  const handleTaskSetClick = (tasksetId: string) => {
    router.push(`/taskset?id=${encodeURIComponent(tasksetId)}`);
  };

  const handleFileUpload = async (file: File) => {
    try {
      setIsUploading(true);
      const response = await uploadTasksYaml(file);

      if (response.success) {
        setToastMessage(
          `Successfully uploaded ${file.name}. ${response.tasks_created} tasks created, ${response.tasks_updated} tasks updated.`
        );
        setIsUploadModalOpen(false);

        // Reload the page after 2 seconds to show new tasks
        setTimeout(() => {
          window.location.reload();
        }, 2000);
      } else {
        setToastMessage(response.message || 'Upload failed');
        setTimeout(() => {
          setToastMessage(null);
        }, 3000);
      }
    } catch (err) {
      setToastMessage(
        err instanceof Error
          ? `Upload failed: ${err.message}`
          : 'Failed to upload file'
      );
      setTimeout(() => {
        setToastMessage(null);
      }, 3000);
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
      {toastMessage && (
        <div className='fixed bottom-4 right-4 z-50 px-4 py-3 bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg shadow-lg flex items-center gap-3 min-w-[300px] max-w-[500px] animate-in slide-in-from-bottom-2'>
          <div className='flex-1'>
            <p
              className={`text-sm ${
                toastMessage.includes('Successfully') ||
                toastMessage.includes('successfully')
                  ? 'text-text-success'
                  : 'text-text-danger'
              }`}
            >
              {toastMessage}
            </p>
          </div>
          <button
            onClick={() => setToastMessage(null)}
            className='text-text-disabled hover:text-text transition-colors text-lg leading-none'
            aria-label='Close notification'
          >
            ×
          </button>
        </div>
      )}
    </>
  );
};

// Legacy export for backward compatibility
const ProjectView = TaskSetView;
export default TaskSetView;
export { ProjectView };
