'use client';

import { useRouter, useSearchParams } from 'next/navigation';
import React, {
  useCallback,
  useEffect,
  useMemo,
  useRef,
  useState,
} from 'react';

import Button from '@/components/base/ui/button';
import Modal from '@/components/base/ui/modal';
import Toast from '@/components/base/ui/toast';
import FileUpload from '@/components/file-upload';
import { TagsDisplay } from '@/components/tags-display';
import Layout from '@/layouts/common';
import {
  bulkAddTags,
  downloadTasksYaml,
  getTaskSetResults,
  getTaskSets,
  uploadTasksYaml,
} from '@/services/dataservice';
import { type TaskSet, type TaskSetResults } from '@/types/types';

import AddTagModal from './add-tag-modal';
import ProjectTaskDetailsModal from './task-details-modal';
import TaskInfoModal from './task-info-modal';

interface TaskSetDetailsPageProps {
  tasksetId: string;
}

const TaskSetDetailsPage: React.FC<TaskSetDetailsPageProps> = ({
  tasksetId,
}) => {
  const router = useRouter();
  const searchParams = useSearchParams();

  // Parse URL query parameters for filters
  const initialTaskNameSearch = searchParams.get('taskName') || '';
  const initialAgentInstances = searchParams.get('agentInstances')
    ? new Set(searchParams.get('agentInstances')!.split(',').filter(Boolean))
    : new Set<string>();
  const initialTags = searchParams.get('tags')
    ? new Set(searchParams.get('tags')!.split(',').filter(Boolean))
    : new Set<string>();
  const initialTasksetTags = searchParams.get('tasksetTags')
    ? new Set(searchParams.get('tasksetTags')!.split(',').filter(Boolean))
    : new Set<string>();

  const [taskset, setTaskSet] = useState<TaskSet | null>(null);
  const [results, setResults] = useState<TaskSetResults | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [selectedAgentInstances, setSelectedAgentInstances] = useState<
    Set<string>
  >(initialAgentInstances);
  const [selectedTags, setSelectedTags] = useState<Set<string>>(initialTags);
  const [selectedTasksetTags, setSelectedTasksetTags] =
    useState<Set<string>>(initialTasksetTags);
  const [agentInstanceSearch, setAgentInstanceSearch] = useState('');
  const [tagSearch, setTagSearch] = useState('');
  const [tasksetTagSearch, setTasksetTagSearch] = useState('');
  const [taskNameSearch, setTaskNameSearch] = useState(initialTaskNameSearch);
  const [isAgentInstanceDropdownOpen, setIsAgentInstanceDropdownOpen] =
    useState(false);
  const [isTagDropdownOpen, setIsTagDropdownOpen] = useState(false);
  const [isTasksetTagDropdownOpen, setIsTasksetTagDropdownOpen] =
    useState(false);
  const [selectedTasks, setSelectedTasks] = useState<Set<number>>(new Set());
  const [isCreateDatasetModalOpen, setIsCreateDatasetModalOpen] =
    useState(false);
  const [datasetName, setDatasetName] = useState('');

  const [isCreatingDataset, setIsCreatingDataset] = useState(false);
  const [toastMessage, setToastMessage] = useState<string | null>(null);
  const [toastType, setToastType] = useState<'success' | 'error'>('success');
  const [isUploadModalOpen, setIsUploadModalOpen] = useState(false);
  const [isUploading, setIsUploading] = useState(false);
  const [isDownloading, setIsDownloading] = useState(false);
  const [modalState, setModalState] = useState<{
    isOpen: boolean;
    taskId: number;
    agentInstanceId: string;
    agentChecksum: string;
    agentName: string;
  }>({
    isOpen: false,
    taskId: -1,
    agentInstanceId: '',
    agentChecksum: '',
    agentName: '',
  });
  const [taskInfoModalState, setTaskInfoModalState] = useState<{
    isOpen: boolean;
    taskId: number;
    taskName: string;
  }>({
    isOpen: false,
    taskId: -1,
    taskName: '',
  });
  const [addTagModalState, setAddTagModalState] = useState<{
    isOpen: boolean;
    taskId: number;
    taskName: string;
  }>({
    isOpen: false,
    taskId: -1,
    taskName: '',
  });

  // Track the last URL we generated to avoid syncing when we update it ourselves
  const lastGeneratedUrlRef = useRef<string>('');

  useEffect(() => {
    const fetchProjectData = async () => {
      try {
        setLoading(true);
        setError(null);

        // Fetch all tasksets to find the one we need
        const allTaskSets = await getTaskSets();
        const foundTaskSet = allTaskSets.find(t => t.id === tasksetId);

        if (!foundTaskSet) {
          setError('TaskSet not found');
          setLoading(false);
          return;
        }

        setTaskSet(foundTaskSet);

        // Fetch results for this taskset
        const tasksetResults = await getTaskSetResults(tasksetId);
        setResults(tasksetResults);
      } catch (err) {
        setError(
          err instanceof Error ? err.message : 'Failed to load project data'
        );
      } finally {
        setLoading(false);
      }
    };

    if (tasksetId) {
      fetchProjectData();
    }
  }, [tasksetId]);

  // Sync state with URL parameters when they change externally (e.g., back/forward navigation, shared links)
  useEffect(() => {
    const currentUrl = searchParams.toString();

    // If this URL matches what we last generated, don't sync (we just updated it ourselves)
    if (currentUrl === lastGeneratedUrlRef.current) {
      return;
    }

    const urlTaskName = searchParams.get('taskName') || '';
    const urlAgentInstances = searchParams.get('agentInstances')
      ? new Set(searchParams.get('agentInstances')!.split(',').filter(Boolean))
      : new Set<string>();
    const urlTags = searchParams.get('tags')
      ? new Set(searchParams.get('tags')!.split(',').filter(Boolean))
      : new Set<string>();
    const urlTasksetTags = searchParams.get('tasksetTags')
      ? new Set(searchParams.get('tasksetTags')!.split(',').filter(Boolean))
      : new Set<string>();

    // Update state from URL params
    if (taskNameSearch !== urlTaskName) {
      setTaskNameSearch(urlTaskName);
    }

    // Compare Sets by converting to sorted arrays
    const currentAgentInstances = Array.from(selectedAgentInstances).sort();
    const urlAgentInstancesArray = Array.from(urlAgentInstances).sort();
    if (
      currentAgentInstances.length !== urlAgentInstancesArray.length ||
      !currentAgentInstances.every(
        (val, idx) => val === urlAgentInstancesArray[idx]
      )
    ) {
      setSelectedAgentInstances(urlAgentInstances);
    }

    const currentTags = Array.from(selectedTags).sort();
    const urlTagsArray = Array.from(urlTags).sort();
    if (
      currentTags.length !== urlTagsArray.length ||
      !currentTags.every((val, idx) => val === urlTagsArray[idx])
    ) {
      setSelectedTags(urlTags);
    }

    const currentTasksetTags = Array.from(selectedTasksetTags).sort();
    const urlTasksetTagsArray = Array.from(urlTasksetTags).sort();
    if (
      currentTasksetTags.length !== urlTasksetTagsArray.length ||
      !currentTasksetTags.every((val, idx) => val === urlTasksetTagsArray[idx])
    ) {
      setSelectedTasksetTags(urlTasksetTags);
    }

    // Update ref to prevent re-syncing when state updates trigger this effect again
    lastGeneratedUrlRef.current = currentUrl;
  }, [
    searchParams,
    taskNameSearch,
    selectedAgentInstances,
    selectedTags,
    selectedTasksetTags,
  ]);

  // Update URL when filters change
  useEffect(() => {
    const params = new URLSearchParams();

    if (taskNameSearch.trim()) {
      params.set('taskName', taskNameSearch.trim());
    }

    if (selectedAgentInstances.size > 0) {
      params.set(
        'agentInstances',
        Array.from(selectedAgentInstances).join(',')
      );
    }

    if (selectedTags.size > 0) {
      params.set('tags', Array.from(selectedTags).sort().join(','));
    }

    if (selectedTasksetTags.size > 0) {
      params.set(
        'tasksetTags',
        Array.from(selectedTasksetTags).sort().join(',')
      );
    }

    // Always include the taskset ID as a query parameter
    params.set('id', tasksetId);
    const queryString = params.toString();
    const newUrl = `/taskset?${queryString}`;

    // Track this URL so we don't sync it back to state
    lastGeneratedUrlRef.current = queryString;
    router.replace(newUrl, { scroll: false });
  }, [
    taskNameSearch,
    selectedAgentInstances,
    selectedTags,
    selectedTasksetTags,
    tasksetId,
    router,
  ]);

  // Create a map for quick lookup of results
  const resultsMap = useMemo(() => {
    if (!results)
      return new Map<string, { success_count: number; total_count: number }>();
    const map = new Map<
      string,
      { success_count: number; total_count: number }
    >();
    results.results.forEach(result => {
      const key = `${result.task_id}_${result.agent_instance_id}`;
      map.set(key, {
        success_count: result.success_count,
        total_count: result.total_count,
      });
    });
    return map;
  }, [results]);

  // Get result counts for a task and agent instance
  const getResultCounts = (
    taskId: number,
    agentInstanceId: string
  ): { success_count: number; total_count: number } | null => {
    const key = `${taskId}_${agentInstanceId}`;
    return resultsMap.get(key) || null;
  };

  // Extract all unique tags from tasks
  const allTags = useMemo(() => {
    if (!results) return new Set<string>();
    const tagsSet = new Set<string>();
    results.tasks.forEach(task => {
      if (task.tags) {
        Object.entries(task.tags).forEach(([key, value]) => {
          tagsSet.add(`${key}:${value}`);
        });
      }
    });
    return tagsSet;
  }, [results]);

  // Separate tags into taskset tags and regular tags
  const tasksetTags = useMemo(() => {
    const tasksetSet = new Set<string>();
    allTags.forEach(tag => {
      if (tag.startsWith('taskset_')) {
        tasksetSet.add(tag);
      }
    });
    return tasksetSet;
  }, [allTags]);

  const regularTags = useMemo(() => {
    const regularSet = new Set<string>();
    allTags.forEach(tag => {
      if (!tag.startsWith('taskset_')) {
        regularSet.add(tag);
      }
    });
    return regularSet;
  }, [allTags]);

  // Filter tasks based on selected tags (both regular and taskset tags) and task name search
  const filteredTasks = useMemo(() => {
    if (!results) return [];

    let tasks = results.tasks;

    // Filter by tags if any are selected
    if (selectedTags.size > 0 || selectedTasksetTags.size > 0) {
      // Combine both tag sets for filtering
      const allSelectedTags = new Set([
        ...Array.from(selectedTags),
        ...Array.from(selectedTasksetTags),
      ]);

      // Filter tasks to show only those with selected tags
      tasks = tasks.filter(task => {
        if (!task.tags || Object.keys(task.tags).length === 0) {
          // Tasks with no tags are not shown when tags are selected
          return false;
        }

        // Check if task has any of the selected tags (regular or taskset)
        return Object.entries(task.tags).some(([key, value]) =>
          allSelectedTags.has(`${key}:${value}`)
        );
      });
    }

    // Filter by task name search if search query exists
    // Matches anywhere in the task name (not just from the start)
    if (taskNameSearch.trim()) {
      const searchLower = taskNameSearch.toLowerCase().trim();
      tasks = tasks.filter(task =>
        task.task_name.toLowerCase().includes(searchLower)
      );
    }

    return tasks;
  }, [results, selectedTags, selectedTasksetTags, taskNameSearch]);

  // Filter agent instances based on selection
  const filteredAgentInstances = useMemo(() => {
    if (!results) return [];
    // If no agent instances are selected, show all
    if (selectedAgentInstances.size === 0) return results.agent_instances;

    // Filter to show only selected agent instances
    return results.agent_instances.filter(instance =>
      selectedAgentInstances.has(instance.agent_instance_id)
    );
  }, [results, selectedAgentInstances]);

  // Calculate agent performance stats (sum across filtered tasks)
  const agentPerformance = useMemo(() => {
    if (!results) return new Map<string, { success: number; total: number }>();
    const performance = new Map<string, { success: number; total: number }>();

    filteredAgentInstances.forEach(instance => {
      let success = 0;
      let total = 0;

      filteredTasks.forEach(task => {
        const counts = getResultCounts(
          task.task_id,
          instance.agent_instance_id
        );
        if (counts) {
          success += counts.success_count;
          total += counts.total_count;
        }
      });

      performance.set(instance.agent_instance_id, { success, total });
    });

    return performance;
  }, [results, resultsMap, filteredTasks, filteredAgentInstances]);

  const handleAgentInstanceToggle = (instanceId: string) => {
    setSelectedAgentInstances(prev => {
      const newSet = new Set(prev);
      if (newSet.has(instanceId)) {
        newSet.delete(instanceId);
      } else {
        newSet.add(instanceId);
      }
      return newSet;
    });
  };

  const handleTagToggle = (tag: string) => {
    setSelectedTags(prev => {
      const newSet = new Set(prev);
      if (newSet.has(tag)) {
        newSet.delete(tag);
      } else {
        newSet.add(tag);
      }
      return newSet;
    });
  };

  const handleSelectAllAgentInstances = () => {
    if (!results) return;
    if (selectedAgentInstances.size === results.agent_instances.length) {
      setSelectedAgentInstances(new Set());
    } else {
      setSelectedAgentInstances(
        new Set(results.agent_instances.map(i => i.agent_instance_id))
      );
    }
  };

  const handleSelectAllTags = () => {
    if (selectedTags.size === regularTags.size) {
      setSelectedTags(new Set());
    } else {
      setSelectedTags(new Set(regularTags));
    }
  };

  const handleTasksetTagToggle = (tag: string) => {
    setSelectedTasksetTags(prev => {
      const newSet = new Set(prev);
      if (newSet.has(tag)) {
        newSet.delete(tag);
      } else {
        newSet.add(tag);
      }
      return newSet;
    });
  };

  const handleSelectAllTasksetTags = () => {
    if (selectedTasksetTags.size === tasksetTags.size) {
      setSelectedTasksetTags(new Set());
    } else {
      setSelectedTasksetTags(new Set(tasksetTags));
    }
  };

  const handleTaskToggle = (taskId: number) => {
    setSelectedTasks(prev => {
      const newSet = new Set(prev);
      if (newSet.has(taskId)) {
        newSet.delete(taskId);
      } else {
        newSet.add(taskId);
      }
      return newSet;
    });
  };

  const handleSelectAllTasks = () => {
    if (!results) return;
    if (selectedTasks.size === filteredTasks.length) {
      setSelectedTasks(new Set());
    } else {
      setSelectedTasks(new Set(filteredTasks.map(t => t.task_id)));
    }
  };

  const handleCreateTaskSet = async () => {
    if (!datasetName.trim() || selectedTasks.size === 0) return;

    try {
      setIsCreatingDataset(true);

      // Add tags to the selected tasks
      const tagName = `taskset_${datasetName.trim()}`;
      await bulkAddTags({
        task_ids: Array.from(selectedTasks),
        tags: [tagName],
      });

      // Success - show toast and reset
      setToastType('success');
      setToastMessage('Dataset created successfully!');
      setIsCreateDatasetModalOpen(false);
      setDatasetName('');

      setSelectedTasks(new Set());

      // Hide toast after 2 seconds
      setTimeout(() => {
        setToastMessage('Successfully created taskset');
        window.location.reload();
      }, 2000);
    } catch (err) {
      setToastType('error');
      setToastMessage(
        err instanceof Error ? err.message : 'Failed to create taskset'
      );
    } finally {
      setIsCreatingDataset(false);
    }
  };

  const handleTagAddSuccess = useCallback(() => {
    setToastType('success');
    setToastMessage('Successfully added tag(s) to task');
    // Reload data after 1 second to show updated tags
    setTimeout(() => {
      window.location.reload();
    }, 1000);
  }, []);

  const handleOpenAddTagModal = useCallback(
    (taskId: number, taskName: string) => {
      setAddTagModalState({
        isOpen: true,
        taskId,
        taskName,
      });
    },
    []
  );

  const handleCloseAddTagModal = useCallback(() => {
    setAddTagModalState({
      isOpen: false,
      taskId: -1,
      taskName: '',
    });
  }, []);

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

  const handleDownloadYaml = async () => {
    if (selectedTasks.size === 0) {
      setToastType('error');
      setToastMessage('Please select tasks to download');
      return;
    }

    try {
      setIsDownloading(true);
      const blob = await downloadTasksYaml(tasksetId, {
        task_ids: Array.from(selectedTasks),
      });

      // Create a download link and trigger it
      const url = window.URL.createObjectURL(blob);
      const link = document.createElement('a');
      link.href = url;
      link.download = `${tasksetId}_tasks_${Date.now()}.yaml`;
      document.body.appendChild(link);
      link.click();
      document.body.removeChild(link);
      window.URL.revokeObjectURL(url);

      setToastType('success');
      setToastMessage(
        `Successfully downloaded YAML file with ${selectedTasks.size} tasks`
      );
    } catch (err) {
      setToastType('error');
      setToastMessage(
        err instanceof Error
          ? `Download failed: ${err.message}`
          : 'Failed to download YAML file'
      );
    } finally {
      setIsDownloading(false);
    }
  };

  // Filter agent instances based on search
  const filteredAgentInstancesForSearch = useMemo(() => {
    if (!results) return [];
    if (!agentInstanceSearch) return results.agent_instances;

    const searchLower = agentInstanceSearch.toLowerCase();
    return results.agent_instances.filter(
      instance =>
        instance.agent_name.toLowerCase().includes(searchLower) ||
        instance.agent_instance_id.toLowerCase().includes(searchLower)
    );
  }, [results, agentInstanceSearch]);

  // Helper function to format tag for display (show only value, not key)
  const formatTagForDisplay = (tag: string): string => {
    // Tag format is "key:value", e.g., "priority:high" or "taskset_MyDataset:MyDataset"
    const [, value] = tag.split(':');
    if (!value) return tag; // Fallback if no colon found
    return value;
  };

  // Helper function to format taskset tag for display (remove key and taskset_ prefix)
  const formatTasksetTagForDisplay = formatTagForDisplay;

  // Filter regular tags based on search
  const filteredTagsForSearch = useMemo(() => {
    if (!tagSearch) return Array.from(regularTags).sort();

    const searchLower = tagSearch.toLowerCase();
    return Array.from(regularTags)
      .filter(tag => {
        // Search in both the full tag and the display value
        const displayValue = formatTagForDisplay(tag);
        return (
          tag.toLowerCase().includes(searchLower) ||
          displayValue.toLowerCase().includes(searchLower)
        );
      })
      .sort();
  }, [regularTags, tagSearch]);

  // Filter taskset tags based on search
  const filteredTasksetTagsForSearch = useMemo(() => {
    if (!tasksetTagSearch) return Array.from(tasksetTags).sort();

    const searchLower = tasksetTagSearch.toLowerCase();
    return Array.from(tasksetTags)
      .filter(tag => {
        // Search in both the full tag and the display value
        const displayValue = formatTasksetTagForDisplay(tag);
        return (
          tag.toLowerCase().includes(searchLower) ||
          displayValue.toLowerCase().includes(searchLower)
        );
      })
      .sort();
  }, [tasksetTags, tasksetTagSearch]);

  if (loading) {
    return (
      <Layout title='TaskSet Details'>
        <div className='flex justify-center p-8' data-testid='taskset-loading'>
          <div className='animate-spin rounded-full h-8 w-8 border-b-2 border-blue-400'></div>
        </div>
      </Layout>
    );
  }

  if (error || !taskset) {
    return (
      <Layout title='TaskSet Details'>
        <div
          className='p-8 text-center text-text-disabled'
          data-testid='taskset-error'
        >
          {error || 'TaskSet not found'}
        </div>
      </Layout>
    );
  }

  return (
    <Layout title={`TaskSet: ${taskset.name}`}>
      <div className='mb-6'>
        <button
          onClick={() => router.back()}
          className='text-text-disabled hover:text-text transition-colors text-sm mb-4'
        >
          ← Back
        </button>
        <div className='bg-elevation-surface-raised rounded-lg p-6 border border-elevation-surface-overlay'>
          <h1 className='text-2xl font-semibold text-text mb-2'>
            {taskset.name}
          </h1>
          {taskset.description && (
            <p className='text-text-subtlest text-sm mb-4'>
              {taskset.description}
            </p>
          )}
          <div className='text-text-disabled text-xs'>
            Created: {new Date(taskset.created_at).toLocaleDateString()}
          </div>
        </div>
      </div>

      <div className='backdrop-blur-sm border bg-elevation-surface border-elevation-surface-raised rounded-xl overflow-hidden'>
        <div className='px-6 py-4 border-b border-elevation-surface-raised bg-elevation-surface-raised'>
          <div className='flex items-center justify-between'>
            <div>
              <h2 className='text-[18px] font-semibold text-text leading-6'>
                Task Results
              </h2>
              <p className='text-text-subtlest text-[14px] mt-1 leading-5'>
                Results matrix showing success/failure for each task and agent
                instance
              </p>
            </div>
            <div className='flex items-center gap-3'>
              <Button
                onClick={() => setIsUploadModalOpen(true)}
                variant='default'
              >
                Upload Tasks
              </Button>
              {selectedTasks.size > 0 && (
                <>
                  <Button
                    onClick={handleDownloadYaml}
                    variant='default'
                    disabled={isDownloading}
                  >
                    {isDownloading
                      ? 'Downloading...'
                      : `Download YAML (${selectedTasks.size})`}
                  </Button>
                  <Button
                    onClick={() => setIsCreateDatasetModalOpen(true)}
                    variant='default'
                  >
                    Create TaskSet ({selectedTasks.size} tasks)
                  </Button>
                </>
              )}
            </div>
          </div>
        </div>

        {/* Filters */}
        {results && (
          <div className='px-6 py-4 border-b border-elevation-surface-overlay bg-elevation-surface-raised flex flex-wrap gap-6'>
            {/* Task Name Search */}
            <div className='flex-1 min-w-[300px]'>
              <label
                htmlFor='task-name-search'
                className='text-sm font-semibold text-text block mb-2'
              >
                Search Tasks
              </label>
              <input
                id='task-name-search'
                type='text'
                value={taskNameSearch}
                onChange={e => setTaskNameSearch(e.target.value)}
                placeholder='Search by task name...'
                className='w-full px-3 py-2 bg-elevation-surface border border-elevation-surface-overlay rounded text-sm text-text placeholder-text-disabled focus:outline-none focus:ring-2 focus:ring-border-focused'
              />
            </div>

            {/* Agent Instance Filter */}
            <div className='flex-1 min-w-[300px]'>
              <label className='text-sm font-semibold text-text block mb-2'>
                Agent Instances ({selectedAgentInstances.size}/
                {results.agent_instances.length})
              </label>

              {/* Dropdown */}
              <div className='relative mb-2'>
                <button
                  type='button'
                  onClick={() => {
                    setIsAgentInstanceDropdownOpen(
                      !isAgentInstanceDropdownOpen
                    );
                    setIsTagDropdownOpen(false);
                  }}
                  className='w-full px-3 py-2 bg-elevation-surface border border-elevation-surface-overlay rounded text-sm text-text text-left flex items-center justify-between hover:bg-elevation-surface-raised transition-colors'
                >
                  <span className='text-text-disabled'>
                    {selectedAgentInstances.size === 0
                      ? 'Select agent instances...'
                      : `${selectedAgentInstances.size} selected`}
                  </span>
                  <span className='text-text-disabled'>▼</span>
                </button>

                {isAgentInstanceDropdownOpen && (
                  <>
                    <div
                      className='fixed inset-0 z-10'
                      onClick={() => setIsAgentInstanceDropdownOpen(false)}
                    />
                    <div className='absolute z-20 w-full mt-1 bg-elevation-surface border border-elevation-surface-overlay rounded shadow-lg max-h-64 overflow-hidden flex flex-col'>
                      {/* Search Input */}
                      <div className='p-2 border-b border-elevation-surface-overlay'>
                        <input
                          type='text'
                          value={agentInstanceSearch}
                          onChange={e => setAgentInstanceSearch(e.target.value)}
                          placeholder='Search agent instances...'
                          className='w-full px-2 py-1.5 text-sm bg-elevation-surface-sunken border border-elevation-surface-overlay rounded text-text placeholder-text-disabled focus:outline-none focus:ring-2 focus:ring-border-focused'
                          onClick={e => e.stopPropagation()}
                        />
                      </div>

                      {/* Select All / Deselect All */}
                      <div className='px-2 py-1 border-b border-elevation-surface-overlay'>
                        <button
                          onClick={handleSelectAllAgentInstances}
                          className='text-xs text-text-disabled hover:text-text transition-colors'
                        >
                          {selectedAgentInstances.size ===
                          results.agent_instances.length
                            ? 'Deselect All'
                            : 'Select All'}
                        </button>
                      </div>

                      {/* Options List */}
                      <div className='overflow-y-auto max-h-48'>
                        {filteredAgentInstancesForSearch.length === 0 ? (
                          <div className='px-3 py-2 text-sm text-text-disabled text-center'>
                            No matches found
                          </div>
                        ) : (
                          filteredAgentInstancesForSearch.map(instance => (
                            <label
                              key={instance.agent_instance_id}
                              className='flex items-center gap-2 px-3 py-2 hover:bg-elevation-surface-raised cursor-pointer'
                              onClick={e => e.stopPropagation()}
                            >
                              <input
                                type='checkbox'
                                checked={selectedAgentInstances.has(
                                  instance.agent_instance_id
                                )}
                                onChange={() =>
                                  handleAgentInstanceToggle(
                                    instance.agent_instance_id
                                  )
                                }
                                className='w-4 h-4 rounded border-elevation-surface-overlay text-background-accent-gray-subtlest focus:ring-2 focus:ring-border-focused'
                              />
                              <span
                                className='text-sm text-text truncate flex-1'
                                title={instance.agent_name}
                              >
                                {instance.agent_name}
                              </span>
                            </label>
                          ))
                        )}
                      </div>
                    </div>
                  </>
                )}
              </div>

              {/* Selected Agent Instances */}
              {selectedAgentInstances.size > 0 && (
                <div className='flex flex-wrap gap-2'>
                  {results.agent_instances
                    .filter(instance =>
                      selectedAgentInstances.has(instance.agent_instance_id)
                    )
                    .map(instance => (
                      <button
                        key={instance.agent_instance_id}
                        onClick={() =>
                          handleAgentInstanceToggle(instance.agent_instance_id)
                        }
                        className='px-2 py-1 text-xs bg-elevation-surface-raised border border-elevation-surface-overlay rounded text-text hover:bg-elevation-surface-sunken transition-colors flex items-center gap-1'
                      >
                        <span
                          className='truncate max-w-[150px]'
                          title={instance.agent_name}
                        >
                          {instance.agent_name}
                        </span>
                        <span className='text-text-disabled'>×</span>
                      </button>
                    ))}
                </div>
              )}
            </div>

            {/* Taskset Tags Filter */}
            {tasksetTags.size > 0 && (
              <div className='flex-1 min-w-[300px]'>
                <label className='text-sm font-semibold text-text block mb-2'>
                  Taskset ({selectedTasksetTags.size}/{tasksetTags.size})
                </label>

                {/* Dropdown */}
                <div className='relative mb-2'>
                  <button
                    type='button'
                    onClick={() => {
                      setIsTasksetTagDropdownOpen(!isTasksetTagDropdownOpen);
                      setIsAgentInstanceDropdownOpen(false);
                      setIsTagDropdownOpen(false);
                    }}
                    className='w-full px-3 py-2 bg-elevation-surface border border-elevation-surface-overlay rounded text-sm text-text text-left flex items-center justify-between hover:bg-elevation-surface-raised transition-colors'
                  >
                    <span className='text-text-disabled'>
                      {selectedTasksetTags.size === 0
                        ? 'Select taskset tags...'
                        : `${selectedTasksetTags.size} selected`}
                    </span>
                    <span className='text-text-disabled'>▼</span>
                  </button>

                  {isTasksetTagDropdownOpen && (
                    <>
                      <div
                        className='fixed inset-0 z-10'
                        onClick={() => setIsTasksetTagDropdownOpen(false)}
                      />
                      <div className='absolute z-20 w-full mt-1 bg-elevation-surface border border-elevation-surface-overlay rounded shadow-lg max-h-64 overflow-hidden flex flex-col'>
                        {/* Search Input */}
                        <div className='p-2 border-b border-elevation-surface-overlay'>
                          <input
                            type='text'
                            value={tasksetTagSearch}
                            onChange={e => setTasksetTagSearch(e.target.value)}
                            placeholder='Search taskset tags...'
                            className='w-full px-2 py-1.5 text-sm bg-elevation-surface-sunken border border-elevation-surface-overlay rounded text-text placeholder-text-disabled focus:outline-none focus:ring-2 focus:ring-border-focused'
                            onClick={e => e.stopPropagation()}
                          />
                        </div>

                        {/* Select All / Deselect All */}
                        <div className='px-2 py-1 border-b border-elevation-surface-overlay'>
                          <button
                            onClick={handleSelectAllTasksetTags}
                            className='text-xs text-text-disabled hover:text-text transition-colors'
                          >
                            {selectedTasksetTags.size === tasksetTags.size
                              ? 'Deselect All'
                              : 'Select All'}
                          </button>
                        </div>

                        {/* Options List */}
                        <div className='overflow-y-auto max-h-48'>
                          {filteredTasksetTagsForSearch.length === 0 ? (
                            <div className='px-3 py-2 text-sm text-text-disabled text-center'>
                              No matches found
                            </div>
                          ) : (
                            filteredTasksetTagsForSearch.map(tag => (
                              <label
                                key={tag}
                                className='flex items-center gap-2 px-3 py-2 hover:bg-elevation-surface-raised cursor-pointer'
                                onClick={e => e.stopPropagation()}
                              >
                                <input
                                  type='checkbox'
                                  checked={selectedTasksetTags.has(tag)}
                                  onChange={() => handleTasksetTagToggle(tag)}
                                  className='w-4 h-4 rounded border-elevation-surface-overlay text-background-accent-gray-subtlest focus:ring-2 focus:ring-border-focused'
                                />
                                <span className='text-sm text-text'>
                                  {formatTasksetTagForDisplay(tag)}
                                </span>
                              </label>
                            ))
                          )}
                        </div>
                      </div>
                    </>
                  )}
                </div>

                {/* Selected Taskset Tags */}
                {selectedTasksetTags.size > 0 && (
                  <div className='flex flex-wrap gap-2'>
                    {Array.from(selectedTasksetTags)
                      .sort()
                      .map(tag => (
                        <button
                          key={tag}
                          onClick={() => handleTasksetTagToggle(tag)}
                          className='px-2 py-1 text-xs bg-elevation-surface-raised border border-elevation-surface-overlay rounded text-text hover:bg-elevation-surface-sunken transition-colors flex items-center gap-1'
                        >
                          <span>{formatTasksetTagForDisplay(tag)}</span>
                          <span className='text-text-disabled'>×</span>
                        </button>
                      ))}
                  </div>
                )}
              </div>
            )}

            {/* Regular Tags Filter */}
            {regularTags.size > 0 && (
              <div className='flex-1 min-w-[300px]'>
                <label className='text-sm font-semibold text-text block mb-2'>
                  Tags ({selectedTags.size}/{regularTags.size})
                </label>

                {/* Dropdown */}
                <div className='relative mb-2'>
                  <button
                    type='button'
                    onClick={() => {
                      setIsTagDropdownOpen(!isTagDropdownOpen);
                      setIsAgentInstanceDropdownOpen(false);
                      setIsTasksetTagDropdownOpen(false);
                    }}
                    className='w-full px-3 py-2 bg-elevation-surface border border-elevation-surface-overlay rounded text-sm text-text text-left flex items-center justify-between hover:bg-elevation-surface-raised transition-colors'
                  >
                    <span className='text-text-disabled'>
                      {selectedTags.size === 0
                        ? 'Select tags...'
                        : `${selectedTags.size} selected`}
                    </span>
                    <span className='text-text-disabled'>▼</span>
                  </button>

                  {isTagDropdownOpen && (
                    <>
                      <div
                        className='fixed inset-0 z-10'
                        onClick={() => setIsTagDropdownOpen(false)}
                      />
                      <div className='absolute z-20 w-full mt-1 bg-elevation-surface border border-elevation-surface-overlay rounded shadow-lg max-h-64 overflow-hidden flex flex-col'>
                        {/* Search Input */}
                        <div className='p-2 border-b border-elevation-surface-overlay'>
                          <input
                            type='text'
                            value={tagSearch}
                            onChange={e => setTagSearch(e.target.value)}
                            placeholder='Search tags...'
                            className='w-full px-2 py-1.5 text-sm bg-elevation-surface-sunken border border-elevation-surface-overlay rounded text-text placeholder-text-disabled focus:outline-none focus:ring-2 focus:ring-border-focused'
                            onClick={e => e.stopPropagation()}
                          />
                        </div>

                        {/* Select All / Deselect All */}
                        <div className='px-2 py-1 border-b border-elevation-surface-overlay'>
                          <button
                            onClick={handleSelectAllTags}
                            className='text-xs text-text-disabled hover:text-text transition-colors'
                          >
                            {selectedTags.size === regularTags.size
                              ? 'Deselect All'
                              : 'Select All'}
                          </button>
                        </div>

                        {/* Options List */}
                        <div className='overflow-y-auto max-h-48'>
                          {filteredTagsForSearch.length === 0 ? (
                            <div className='px-3 py-2 text-sm text-text-disabled text-center'>
                              No matches found
                            </div>
                          ) : (
                            filteredTagsForSearch.map(tag => (
                              <label
                                key={tag}
                                className='flex items-center gap-2 px-3 py-2 hover:bg-elevation-surface-raised cursor-pointer'
                                onClick={e => e.stopPropagation()}
                              >
                                <input
                                  type='checkbox'
                                  checked={selectedTags.has(tag)}
                                  onChange={() => handleTagToggle(tag)}
                                  className='w-4 h-4 rounded border-elevation-surface-overlay text-background-accent-gray-subtlest focus:ring-2 focus:ring-border-focused'
                                />
                                <span className='text-sm text-text'>
                                  {formatTagForDisplay(tag)}
                                </span>
                              </label>
                            ))
                          )}
                        </div>
                      </div>
                    </>
                  )}
                </div>

                {/* Selected Tags */}
                {selectedTags.size > 0 && (
                  <div className='flex flex-wrap gap-2'>
                    {Array.from(selectedTags)
                      .sort()
                      .map(tag => (
                        <button
                          key={tag}
                          onClick={() => handleTagToggle(tag)}
                          className='px-2 py-1 text-xs bg-elevation-surface-raised border border-elevation-surface-overlay rounded text-text hover:bg-elevation-surface-sunken transition-colors flex items-center gap-1'
                        >
                          <span>{formatTagForDisplay(tag)}</span>
                          <span className='text-text-disabled'>×</span>
                        </button>
                      ))}
                  </div>
                )}
              </div>
            )}
          </div>
        )}

        <div className='overflow-x-auto'>
          {!results || filteredTasks.length === 0 ? (
            <div className='text-center py-8 text-text-disabled'>
              {results && results.tasks.length === 0
                ? 'No tasks found in this taskset'
                : 'No tasks match the selected filters'}
            </div>
          ) : (
            <>
              {filteredAgentInstances.length === 0 && (
                <div className='px-6 py-3 bg-elevation-surface-raised border-b border-elevation-surface-overlay'>
                  <p className='text-sm text-text-disabled'>
                    {results && results.agent_instances.length === 0
                      ? 'No agent instances found in this taskset. Tasks are shown below.'
                      : 'No agent instances selected. Tasks are shown below.'}
                  </p>
                </div>
              )}
              <table
                className='w-full border-collapse'
                data-testid='project-results-table'
              >
                <thead>
                  <tr className='border-b border-elevation-surface-overlay'>
                    <th className='px-4 py-3 text-left text-sm font-semibold text-text sticky left-0 bg-elevation-surface z-10 border-r border-elevation-surface-overlay min-w-[200px]'>
                      <div className='flex items-center gap-2'>
                        <input
                          type='checkbox'
                          checked={
                            filteredTasks.length > 0 &&
                            selectedTasks.size === filteredTasks.length
                          }
                          onChange={handleSelectAllTasks}
                          className='w-4 h-4 rounded border-elevation-surface-overlay text-background-accent-gray-subtlest focus:ring-2 focus:ring-border-focused'
                        />
                        <span>Task </span>
                      </div>
                    </th>
                    {filteredAgentInstances.map(instance => {
                      const stats = agentPerformance.get(
                        instance.agent_instance_id
                      );
                      const successCount = stats?.success || 0;
                      const totalCount = stats?.total || 0;
                      return (
                        <th
                          key={instance.agent_instance_id}
                          className='px-4 py-3 text-center text-sm font-semibold text-text min-w-[120px]'
                          title={instance.agent_name}
                        >
                          <div className='flex flex-col items-center gap-1'>
                            <span className='truncate max-w-[100px]'>
                              {instance.agent_name}
                            </span>
                            {totalCount > 0 ? (
                              <span className='text-xs font-medium text-text'>
                                <span className='text-text-success'>
                                  {successCount}
                                </span>
                                /{totalCount}
                              </span>
                            ) : (
                              <span className='text-xs text-text-disabled'>
                                {instance.agent_instance_id.split('_').pop()}
                              </span>
                            )}
                          </div>
                        </th>
                      );
                    })}
                  </tr>
                </thead>
                <tbody className='divide-y divide-elevation-surface-overlay'>
                  {filteredTasks.map(task => (
                    <tr
                      key={task.task_id}
                      className='hover:bg-white/5 transition-colors'
                      data-testid={`task-row-${task.task_id}`}
                    >
                      <td className='px-4 py-3 text-sm text-text font-mono sticky left-0 bg-elevation-surface z-10 border-r border-elevation-surface-overlay'>
                        <div className='flex items-start gap-2'>
                          <input
                            type='checkbox'
                            checked={selectedTasks.has(task.task_id)}
                            onChange={() => handleTaskToggle(task.task_id)}
                            onClick={e => e.stopPropagation()}
                            className='mt-1 w-4 h-4 rounded border-elevation-surface-overlay text-background-accent-gray-subtlest focus:ring-2 focus:ring-border-focused'
                          />
                          <div className='flex flex-col gap-1 flex-1'>
                            <div className='flex items-center gap-2'>
                              <button
                                onClick={e => {
                                  e.stopPropagation();
                                  setTaskInfoModalState({
                                    isOpen: true,
                                    taskId: task.task_id,
                                    taskName: task.task_name,
                                  });
                                }}
                                className='text-left hover:text-text-information transition-colors cursor-pointer flex-1'
                              >
                                {task.task_name}
                              </button>
                              <button
                                onClick={e => {
                                  e.stopPropagation();
                                  handleOpenAddTagModal(
                                    task.task_id,
                                    task.task_name
                                  );
                                }}
                                className='px-2 py-1 text-xs bg-elevation-surface-raised border border-elevation-surface-overlay rounded text-text hover:bg-elevation-surface-sunken transition-colors whitespace-nowrap'
                                title='Add tags to this task'
                              >
                                + Tag
                              </button>
                            </div>
                            {task.tags && Object.keys(task.tags).length > 0 && (
                              <div className='mt-1'>
                                <TagsDisplay
                                  tags={task.tags}
                                  maxVisible={3}
                                  modalTitle={`Tags for ${task.task_name}`}
                                />
                              </div>
                            )}
                          </div>
                        </div>
                      </td>
                      {filteredAgentInstances.map(instance => {
                        const counts = getResultCounts(
                          task.task_id,
                          instance.agent_instance_id
                        );
                        const handleCellClick = () => {
                          if (counts && counts.total_count > 0) {
                            setModalState({
                              isOpen: true,
                              taskId: task.task_id,
                              agentInstanceId: instance.agent_instance_id,
                              agentChecksum: instance.agent_checksum,
                              agentName: instance.agent_name,
                            });
                          }
                        };

                        return (
                          <td
                            key={instance.agent_instance_id}
                            className={`px-4 py-3 text-center ${
                              counts && counts.total_count > 0
                                ? 'cursor-pointer hover:bg-white/10'
                                : ''
                            }`}
                            onClick={handleCellClick}
                          >
                            <div
                              className='flex items-center justify-center'
                              data-testid={`result-${task.task_id}-${instance.agent_instance_id}`}
                            >
                              {counts && counts.total_count > 0 ? (
                                <span className='text-sm font-medium text-text'>
                                  <span className='text-text-success'>
                                    {counts.success_count}
                                  </span>
                                  /{counts.total_count}
                                </span>
                              ) : (
                                <span className='text-sm text-text-disabled'>
                                  -
                                </span>
                              )}
                            </div>
                          </td>
                        );
                      })}
                    </tr>
                  ))}
                </tbody>
              </table>
            </>
          )}
        </div>
      </div>

      <ProjectTaskDetailsModal
        isOpen={modalState.isOpen}
        onClose={() =>
          setModalState({
            isOpen: false,
            taskId: -1,
            agentInstanceId: '',
            agentChecksum: '',
            agentName: '',
          })
        }
        taskId={modalState.taskId}
        agentInstanceId={modalState.agentInstanceId}
        agentChecksum={modalState.agentChecksum}
        agentName={modalState.agentName}
      />

      <TaskInfoModal
        isOpen={taskInfoModalState.isOpen}
        onClose={() =>
          setTaskInfoModalState({
            isOpen: false,
            taskId: -1,
            taskName: '',
          })
        }
        taskId={taskInfoModalState.taskId}
        taskName={taskInfoModalState.taskName}
      />

      {/* Upload Tasks Modal */}
      <Modal
        isOpen={isUploadModalOpen}
        onClose={() => {
          if (!isUploading) {
            setIsUploadModalOpen(false);
          }
        }}
        title='Upload Tasks from YAML'
        size='default'
      >
        <div className='flex flex-col gap-4'>
          <div className='text-sm text-text-disabled'>
            Upload a YAML file containing task definitions. The file will be
            validated on the server.
          </div>
          <FileUpload
            onFileSelect={handleFileUpload}
            accept='.yaml,.yml'
            disabled={isUploading}
          />
          {isUploading && (
            <div className='flex items-center gap-2 text-sm text-text-disabled'>
              <div className='animate-spin rounded-full h-4 w-4 border-b-2 border-primary-default'></div>
              <span>Uploading file...</span>
            </div>
          )}
          <div className='flex gap-3 justify-end pt-2'>
            <Button
              variant='ghost'
              onClick={() => {
                setIsUploadModalOpen(false);
              }}
              disabled={isUploading}
            >
              Cancel
            </Button>
          </div>
        </div>
      </Modal>

      {/* Create Dataset Modal */}
      <Modal
        isOpen={isCreateDatasetModalOpen}
        onClose={() => {
          if (!isCreatingDataset) {
            setIsCreateDatasetModalOpen(false);
            setDatasetName('');
          }
        }}
        title='Create New TaskSet'
        size='default'
      >
        <div className='flex flex-col gap-4'>
          <div>
            <label
              htmlFor='dataset-name-input'
              className='block text-sm font-semibold text-text mb-2'
            >
              TaskSet Name <span className='text-text-danger'>*</span>
            </label>
            <input
              id='dataset-name-input'
              type='text'
              value={datasetName}
              onChange={e => setDatasetName(e.target.value)}
              placeholder='Enter dataset name'
              className='w-full px-3 py-2 bg-elevation-surface border border-elevation-surface-overlay rounded text-sm text-text placeholder-text-disabled focus:outline-none focus:ring-2 focus:ring-border-focused'
              disabled={isCreatingDataset}
            />
          </div>

          <div className='text-sm text-text-disabled'>
            Selected tasks: {selectedTasks.size}
          </div>

          <div className='flex gap-3 justify-end pt-2'>
            <Button
              variant='ghost'
              onClick={() => {
                setIsCreateDatasetModalOpen(false);
                setDatasetName('');
              }}
              disabled={isCreatingDataset}
            >
              Cancel
            </Button>
            <Button
              variant='default'
              onClick={handleCreateTaskSet}
              disabled={
                isCreatingDataset ||
                !datasetName.trim() ||
                selectedTasks.size === 0
              }
            >
              {isCreatingDataset ? 'Creating...' : 'Create TaskSet'}
            </Button>
          </div>
        </div>
      </Modal>

      {/* Add Tag Modal */}
      <AddTagModal
        isOpen={addTagModalState.isOpen}
        onClose={handleCloseAddTagModal}
        taskId={addTagModalState.taskId}
        taskName={addTagModalState.taskName}
        onSuccess={handleTagAddSuccess}
      />

      {/* Toast Notification */}
      <Toast
        message={toastMessage || ''}
        type={toastType}
        isOpen={!!toastMessage}
        onClose={() => setToastMessage(null)}
        duration={3000}
      />
    </Layout>
  );
};

export default TaskSetDetailsPage;
