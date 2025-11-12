import React, { useState, useEffect } from 'react';
import Modal from '@/components/base/modal';
import CodeViewer from '@/components/base/codeViewer';
import TacticStepsViewer from '@/components/base/tacticSteps';
import TacticInfoViewer from '@/components/base/tacticInfo';
import cn from 'classnames';
import type { TaskOutput } from '@/types/types';
import { getObservabilityLogs } from '@/services/dataservice';

interface ComparisonItem {
  label: string;
  task: TaskOutput | null;
}

interface ComparisonModalProps {
  isOpen: boolean;
  onClose: () => void;
  items: ComparisonItem[];
  taskId: string;
}

interface TaskLogs {
  [itemIndex: number]: Record<string, unknown> | null;
}

const ComparisonModal: React.FC<ComparisonModalProps> = ({ isOpen, onClose, items, taskId }) => {
  const [activeTab, setActiveTab] = useState<string>('');
  const [taskLogs, setTaskLogs] = useState<TaskLogs>({});
  const [loading, setLoading] = useState<boolean>(false);
  const [error, setError] = useState<string | null>(null);

  // Fetch observability logs when modal opens
  useEffect(() => {
    if (!isOpen || items.length === 0) return;

    const fetchLogs = async () => {
      setLoading(true);
      setError(null);
      const logs: TaskLogs = {};

      try {
        await Promise.all(
          items.map(async (item, index) => {
            if (item.task) {
              try {
                const taskLogs = await getObservabilityLogs(item.task.run_id, item.task.task_id);
                logs[index] = taskLogs;
              } catch (err) {
                console.error(`Error fetching logs for ${item.label}:`, err);
                logs[index] = null;
              }
            } else {
              logs[index] = null;
            }
          })
        );

        setTaskLogs(logs);
      } catch (err) {
        console.error('Error fetching comparison logs:', err);
        setError('Failed to load comparison data');
      } finally {
        setLoading(false);
      }
    };

    fetchLogs();
  }, [isOpen, items]);

  // Define which keys should have custom UI
  const customUIKeys = React.useMemo(() => 
    ['cpp_code', 'cppCode', 'code', 'targetContent', 'lemmaContent', 'statesContent', 'tactic_prediction_explanation', 'tactic_prediction_tactic', 'tactic_info'], []
  );
  
  // Get all available keys from all fetched logs
  const availableKeys = React.useMemo(() => {
    const keysSet = new Set<string>();
    Object.values(taskLogs).forEach(logs => {
      if (logs && typeof logs === 'object') {
        Object.keys(logs).forEach(key => keysSet.add(key));
      }
    });
    return Array.from(keysSet).sort();
  }, [taskLogs]);
  
  const customKeys = React.useMemo(() => 
    availableKeys.filter(key => customUIKeys.includes(key)), [availableKeys, customUIKeys]
  );
  
  const jsonKeys = React.useMemo(() => 
    availableKeys.filter(key => !customUIKeys.includes(key)), [availableKeys, customUIKeys]
  );

  // Reset active tab when details change
  React.useEffect(() => {
    if (availableKeys.length > 0) {
      // Prefer custom UI keys first, then fallback to JSON keys
      const defaultTab = customKeys.length > 0 ? customKeys[0] : jsonKeys[0];
      setActiveTab(defaultTab || '');
    }
  }, [availableKeys, customKeys, jsonKeys]);

  // Helper function to get value from fetched logs
  const getTaskValue = (itemIndex: number, key: string): unknown => {
    const logs = taskLogs[itemIndex];
    if (!logs || typeof logs !== 'object') return null;
    return logs[key];
  };

  // Helper function to render custom UI for specific keys
  const renderCustomContent = (key: string, value: unknown) => {
    // Handle new tactic_info array with structured tactic objects
    if (key === 'tactic_info' && Array.isArray(value)) {
      return (
        <TacticInfoViewer
          tactics={value as Array<{name: string; next_tactic_prediction: string; status: "success" | "failure"; explaination: string; [key: string]: unknown}>}
          title="Tactic Information"
        />
      );
    }

    // Handle legacy tactic prediction arrays - ONLY these keys should be treated as arrays
    if (key === 'tactic_prediction_explanation' && Array.isArray(value)) {
      return (
        <TacticStepsViewer
          steps={value.filter((step): step is string => typeof step === 'string')}
          type="explanation"
          title="Tactic Prediction Explanation"
        />
      );
    }
    
    if (key === 'tactic_prediction_tactic' && Array.isArray(value)) {
      return (
        <TacticStepsViewer
          steps={value.filter((step): step is string => typeof step === 'string')}
          type="tactic"
          title="Tactic Prediction Steps"
        />
      );
    }
    
    // For all other keys, handle as string arrays and render all strings
    let stringValues: string[];
    if (Array.isArray(value)) {
      stringValues = value.filter((item): item is string => typeof item === 'string');
    } else if (typeof value === 'string') {
      stringValues = [value];
    } else {
      return null;
    }
    
    if (stringValues.length === 0) return null;
    
    const lowerKey = key.toLowerCase();
    
    if (lowerKey.includes('cpp') || lowerKey.includes('code')) {
      return (
        <div className="space-y-4">
          {stringValues.map((code, index) => (
            <CodeViewer
              key={index}
              code={code}
              language="cpp"
              filename={`${key}_${index + 1}.cpp`}
            />
          ))}
        </div>
      );
    }
    
    if (lowerKey.includes('target') || lowerKey.includes('lemma') || lowerKey.includes('states')) {
      return (
        <div className="space-y-4">
          {stringValues.map((text, index) => (
            <CodeViewer
              key={index}
              code={text}
              language="text"
              filename={`${key}_${index + 1}.txt`}
            />
          ))}
        </div>
      );
    }
    
    return null;
  };

  // Helper function to render JSON content
  const renderJsonContent = (key: string, value: unknown) => {
    // For all keys except tactic prediction and tactic info ones, handle as string arrays
    if (key !== 'tactic_prediction_explanation' && key !== 'tactic_prediction_tactic' && key !== 'tactic_info' && Array.isArray(value)) {
      const stringValues = value.filter((item): item is string => typeof item === 'string');
      if (stringValues.length > 0) {
        return (
          <div className="space-y-4">
            {stringValues.map((str, index) => (
              <div key={index} className="bg-gray-900/50 border border-white/10 rounded-lg p-4 max-h-96 overflow-auto">
                <div className="text-xs text-gray-400 mb-2">Item {index + 1}</div>
                <pre className="text-sm text-gray-300 whitespace-pre-wrap font-mono">
                  {str}
                </pre>
              </div>
            ))}
          </div>
        );
      }
    }
    
    const jsonString = typeof value === 'string' 
      ? value 
      : JSON.stringify(value, null, 2);
    
    return (
      <div className="bg-gray-900/50 border border-white/10 rounded-lg p-4 max-h-96 overflow-auto">
        <pre className="text-sm text-gray-300 whitespace-pre-wrap font-mono">
          {jsonString}
        </pre>
      </div>
    );
  };

  // Helper function to get tab color based on key
  const getTabColor = (key: string) => {
    const lowerKey = key.toLowerCase();
    if (key === 'tactic_info') return 'purple';
    if (key === 'tactic_prediction_explanation') return 'blue';
    if (key === 'tactic_prediction_tactic') return 'green';
    if (lowerKey.includes('cpp') || lowerKey.includes('code')) return 'blue';
    if (lowerKey.includes('target')) return 'purple';
    if (lowerKey.includes('lemma')) return 'green';
    if (lowerKey.includes('states')) return 'orange';
    return 'gray';
  };

  const getTabColorClasses = (key: string, isActive: boolean) => {
    const color = getTabColor(key);
    if (isActive) {
      return {
        'blue': 'border-blue-400 text-blue-400',
        'purple': 'border-purple-400 text-purple-400',
        'green': 'border-green-400 text-green-400',
        'orange': 'border-orange-400 text-orange-400',
        'gray': 'border-gray-400 text-gray-400'
      }[color];
    }
    return 'border-transparent text-gray-400 hover:text-gray-300';
  };

  return (
    <Modal
      isOpen={isOpen}
      onClose={onClose}
      title={`Compare Task: ${taskId}`}
      size="full"
    >
      <div className="space-y-4 h-full flex flex-col">
        {/* Loading State */}
        {loading && (
          <div className="flex-1 flex items-center justify-center">
            <div className="text-center">
              <div className="animate-spin rounded-full h-8 w-8 border-b-2 border-blue-400 mx-auto mb-4"></div>
              <p className="text-gray-400">Loading comparison data...</p>
            </div>
          </div>
        )}

        {/* Error State */}
        {error && !loading && (
          <div className="flex-1 flex items-center justify-center">
            <div className="text-center text-red-400">
              <p>Error: {error}</p>
            </div>
          </div>
        )}

        {/* Content */}
        {!loading && !error && availableKeys.length > 0 && (
          <>
            {/* Tab Navigation */}
            <div className="flex flex-wrap border-b border-white/10 shrink-0">
              {availableKeys.map(key => (
                <button
                  key={key}
                  onClick={() => setActiveTab(key)}
                  className={cn(
                    "px-4 py-2 text-sm font-medium border-b-2 transition-colors duration-200",
                    getTabColorClasses(key, activeTab === key)
                  )}
                >
                  {key}
                </button>
              ))}
            </div>

            {/* Comparison Content */}
            <div className="flex-1 overflow-hidden">
              {activeTab && (
                <div className="h-full overflow-y-auto">
                  <div className="space-y-4">
                    {items.map((item, index) => {
                      const value = getTaskValue(index, activeTab);
                      const hasData = value !== undefined && value !== null;
                      
                      return (
                        <div key={index} className="border border-white/10 rounded-lg bg-white/5 p-4">
                          <div className="flex items-center justify-between mb-4 shrink-0">
                            <div className="flex flex-col">
                              <h4 className="text-sm font-medium truncate" title={item.label}>
                                {item.label}
                              </h4>
                              {item.task && (
                                <span className="text-xs text-gray-400 font-mono" title={item.task.run_id}>
                                  Run: {item.task.run_id}
                                </span>
                              )}
                            </div>
                            {item.task && (
                              <span className={cn(
                                'px-2 py-0.5 rounded-full text-xs font-semibold border',
                                item.task.status === 'Success' ?
                                  'bg-green-500/20 text-green-300 border-green-500/30' :
                                  'bg-red-500/20 text-red-300 border-red-500/30'
                              )}>
                                {item.task.status}
                              </span>
                            )}
                          </div>
                          
                          <div className="overflow-auto">
                            {!hasData ? (
                              <div className="text-sm text-gray-500 italic text-center py-8">
                                {!item.task ? 'Task not present' : 'No data for this key'}
                              </div>
                            ) : (
                              <>
                                {/* Try custom UI first */}
                                {customKeys.includes(activeTab) 
                                  ? renderCustomContent(activeTab, value)
                                  : renderJsonContent(activeTab, value)
                                }
                              </>
                            )}
                          </div>
                        </div>
                      );
                    })}
                  </div>
                </div>
              )}
            </div>
          </>
        )}
        
        {/* No Data State */}
        {!loading && !error && availableKeys.length === 0 && (
          <div className="text-center text-gray-400 py-8 flex-1 flex items-center justify-center">
            No comparable data available
          </div>
        )}
      </div>
    </Modal>
  );
};

export default ComparisonModal;