'use client';

import axios from 'axios';
import { useRouter } from 'next/navigation';
import React, { useEffect, useMemo, useState } from 'react';

import Button from '@/components/base/ui/button';
import Modal from '@/components/base/ui/modal';
import { config } from '@/config/environment';
import Layout from '@/layouts/common';
import { getTaskSetResults, getTaskSets } from '@/services/dataservice';
import { type TaskSet, type TaskSetResults } from '@/types/types';

import ProjectTaskDetailsModal from './task-details-modal';

interface TaskSetDetailsPageProps {
  tasksetId: string;
}

const TaskSetDetailsPage: React.FC<TaskSetDetailsPageProps> = ({
  tasksetId,
}) => {
  const router = useRouter();
  const [taskset, setTaskSet] = useState<TaskSet | null>(null);
  const [results, setResults] = useState<TaskSetResults | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [selectedAgentInstances, setSelectedAgentInstances] = useState<
    Set<string>
  >(new Set());
  const [selectedTags, setSelectedTags] = useState<Set<string>>(new Set());
  const [agentInstanceSearch, setAgentInstanceSearch] = useState('');
  const [tagSearch, setTagSearch] = useState('');
  const [isAgentInstanceDropdownOpen, setIsAgentInstanceDropdownOpen] =
    useState(false);
  const [isTagDropdownOpen, setIsTagDropdownOpen] = useState(false);
  const [selectedTasks, setSelectedTasks] = useState<Set<number>>(new Set());
  const [isCreateDatasetModalOpen, setIsCreateDatasetModalOpen] =
    useState(false);
  const [datasetName, setDatasetName] = useState('');
  const [datasetDescription, setDatasetDescription] = useState('');
  const [isCreatingDataset, setIsCreatingDataset] = useState(false);
  const [toastMessage, setToastMessage] = useState<string | null>(null);
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

  // Initialize selected agent instances when results load
  useEffect(() => {
    if (results && selectedAgentInstances.size === 0) {
      setSelectedAgentInstances(
        new Set(results.agent_instances.map(i => i.agent_instance_id))
      );
    }
  }, [results, selectedAgentInstances.size]);

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

  // Initialize selected tags when tags are available
  useEffect(() => {
    if (allTags.size > 0 && selectedTags.size === 0) {
      setSelectedTags(new Set(allTags));
    }
  }, [allTags, selectedTags.size]);

  // Filter tasks based on selected tags
  const filteredTasks = useMemo(() => {
    if (!results) return [];
    if (selectedTags.size === 0) return results.tasks;

    return results.tasks.filter(task => {
      if (!task.tags || Object.keys(task.tags).length === 0) {
        // If no tags, only show if "no tags" is selected or all tags are selected
        return selectedTags.size === allTags.size;
      }

      // Check if task has any of the selected tags
      return Object.entries(task.tags).some(([key, value]) =>
        selectedTags.has(`${key}:${value}`)
      );
    });
  }, [results, selectedTags, allTags.size]);

  // Filter agent instances based on selection
  const filteredAgentInstances = useMemo(() => {
    if (!results) return [];
    if (selectedAgentInstances.size === 0) return [];

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
    if (selectedTags.size === allTags.size) {
      setSelectedTags(new Set());
    } else {
      setSelectedTags(new Set(allTags));
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

  const handleCreateDataset = async () => {
    if (!datasetName.trim() || selectedTasks.size === 0) return;

    try {
      setIsCreatingDataset(true);
      await axios.post(`${config.DATA_API}/datasets`, {
        name: datasetName.trim(),
        description: datasetDescription.trim() || undefined,
        task_ids: Array.from(selectedTasks),
        id: tasksetId,
      });

      // Success - show toast and reset
      setToastMessage('Dataset created successfully!');
      setIsCreateDatasetModalOpen(false);
      setDatasetName('');
      setDatasetDescription('');
      setSelectedTasks(new Set());

      // Hide toast after 2 seconds
      setTimeout(() => {
        setToastMessage(null);
      }, 2000);
    } catch (err) {
      setToastMessage(
        err instanceof Error ? err.message : 'Failed to create dataset'
      );
      setTimeout(() => {
        setToastMessage(null);
      }, 2000);
    } finally {
      setIsCreatingDataset(false);
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

  // Filter tags based on search
  const filteredTagsForSearch = useMemo(() => {
    if (!tagSearch) return Array.from(allTags).sort();

    const searchLower = tagSearch.toLowerCase();
    return Array.from(allTags)
      .filter(tag => tag.toLowerCase().includes(searchLower))
      .sort();
  }, [allTags, tagSearch]);

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
            {selectedTasks.size > 0 && (
              <Button
                onClick={() => setIsCreateDatasetModalOpen(true)}
                variant='default'
              >
                Create Dataset ({selectedTasks.size} tasks)
              </Button>
            )}
          </div>
        </div>

        {/* Filters */}
        {results && (
          <div className='px-6 py-4 border-b border-elevation-surface-overlay bg-elevation-surface-raised flex flex-wrap gap-6'>
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

            {/* Tags Filter */}
            {allTags.size > 0 && (
              <div className='flex-1 min-w-[300px]'>
                <label className='text-sm font-semibold text-text block mb-2'>
                  Tags ({selectedTags.size}/{allTags.size})
                </label>

                {/* Dropdown */}
                <div className='relative mb-2'>
                  <button
                    type='button'
                    onClick={() => {
                      setIsTagDropdownOpen(!isTagDropdownOpen);
                      setIsAgentInstanceDropdownOpen(false);
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
                            {selectedTags.size === allTags.size
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
                                <span className='text-sm text-text'>{tag}</span>
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
                          <span>{tag}</span>
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
          ) : filteredAgentInstances.length === 0 ? (
            <div className='text-center py-8 text-text-disabled'>
              {results && results.agent_instances.length === 0
                ? 'No agent instances found in this taskset'
                : 'No agent instances selected'}
            </div>
          ) : (
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
                      <span>Task ID</span>
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
                          <span>{task.task_name}</span>
                          {task.tags && Object.keys(task.tags).length > 0 && (
                            <div className='flex flex-wrap gap-1 mt-1'>
                              {Object.entries(task.tags).map(([key, value]) => (
                                <span
                                  key={`${key}:${value}`}
                                  className='text-xs px-1.5 py-0.5 rounded bg-elevation-surface-raised border border-elevation-surface-overlay text-text-disabled'
                                >
                                  {key}:{value}
                                </span>
                              ))}
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

      {/* Create Dataset Modal */}
      <Modal
        isOpen={isCreateDatasetModalOpen}
        onClose={() => {
          if (!isCreatingDataset) {
            setIsCreateDatasetModalOpen(false);
            setDatasetName('');
            setDatasetDescription('');
          }
        }}
        title='Create New Dataset'
        size='default'
      >
        <div className='flex flex-col gap-4'>
          <div>
            <label
              htmlFor='dataset-name-input'
              className='block text-sm font-semibold text-text mb-2'
            >
              Dataset Name <span className='text-text-danger'>*</span>
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

          <div>
            <label
              htmlFor='dataset-description-textarea'
              className='block text-sm font-semibold text-text mb-2'
            >
              Description
            </label>
            <textarea
              id='dataset-description-textarea'
              value={datasetDescription}
              onChange={e => setDatasetDescription(e.target.value)}
              placeholder='Enter dataset description (optional)'
              rows={4}
              className='w-full px-3 py-2 bg-elevation-surface border border-elevation-surface-overlay rounded text-sm text-text placeholder-text-disabled focus:outline-none focus:ring-2 focus:ring-border-focused resize-none'
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
                setDatasetDescription('');
              }}
              disabled={isCreatingDataset}
            >
              Cancel
            </Button>
            <Button
              variant='default'
              onClick={handleCreateDataset}
              disabled={
                isCreatingDataset ||
                !datasetName.trim() ||
                selectedTasks.size === 0
              }
            >
              {isCreatingDataset ? 'Creating...' : 'Create Dataset'}
            </Button>
          </div>
        </div>
      </Modal>

      {/* Toast Notification */}
      {toastMessage && (
        <div className='fixed bottom-4 right-4 z-50 px-4 py-3 bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg shadow-lg flex items-center gap-3 min-w-[300px] max-w-[500px] animate-in slide-in-from-bottom-2'>
          <div className='flex-1'>
            <p
              className={`text-sm ${
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
    </Layout>
  );
};

export default TaskSetDetailsPage;
