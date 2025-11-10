import React, { useState } from 'react';
import Modal from '@/components/base/modal';
import CodeViewer from '@/components/base/codeViewer';
import TacticStepsViewer from '@/components/base/tacticSteps';
import cn from 'classnames';

interface TaskDetailsModalProps {
  isOpen: boolean;
  onClose: () => void;
  details: Record<string, unknown> | null;
  title?: string;
  taskId?: string;
}

const TaskDetailsModal: React.FC<TaskDetailsModalProps> = ({ isOpen, onClose, details, title = 'Task Details', taskId }) => {
  const [activeTab, setActiveTab] = useState<string>('');

  // Define which keys should have custom UI
  const customUIKeys = React.useMemo(() => 
    ['cpp_code', 'cppCode', 'code', 'targetContent', 'lemmaContent', 'statesContent', 'tactic_prediction_explanation', 'tactic_prediction_tactic'], []
  );
  
  // Get all available keys from details
  const availableKeys = React.useMemo(() => 
    details ? Object.keys(details) : [], [details]
  );
  
  const customKeys = React.useMemo(() => 
    availableKeys.filter(key => customUIKeys.includes(key)), [availableKeys, customUIKeys]
  );
  
  const jsonKeys = React.useMemo(() => 
    availableKeys.filter(key => !customUIKeys.includes(key)), [availableKeys, customUIKeys]
  );

  // Reset active tab when details change
  React.useEffect(() => {
    if (details && availableKeys.length > 0) {
      // Prefer custom UI keys first, then fallback to JSON keys
      const defaultTab = customKeys.length > 0 ? customKeys[0] : jsonKeys[0];
      setActiveTab(defaultTab || '');
    }
  }, [details, availableKeys, customKeys, jsonKeys]);

  if (!details) return null;

  // Helper function to render custom UI for specific keys
  const renderCustomContent = (key: string, value: unknown) => {
    // Handle tactic prediction arrays - ONLY these keys should be treated as arrays
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
    
    // For all other keys, if it's an array, pick the first index (should be string)
    let stringValue: string;
    if (Array.isArray(value)) {
      stringValue = value[0] as string;
    } else if (typeof value === 'string') {
      stringValue = value;
    } else {
      return null;
    }
    
    const lowerKey = key.toLowerCase();
    
    if (lowerKey.includes('cpp') || lowerKey.includes('code')) {
      return (
        <CodeViewer
          code={stringValue}
          language="cpp"
          filename={`${key}.cpp`}
        />
      );
    }
    
    if (lowerKey.includes('target') || lowerKey.includes('lemma') || lowerKey.includes('states')) {
      return (
        <CodeViewer
          code={stringValue}
          language="text"
          filename={`${key}.txt`}
        />
      );
    }
    
    return null;
  };

  // Helper function to render JSON content
  const renderJsonContent = (key: string, value: unknown) => {
    // For all keys except tactic prediction ones, if it's an array, pick the first index
    let processedValue = value;
    if (key !== 'tactic_prediction_explanation' && key !== 'tactic_prediction_tactic' && Array.isArray(value)) {
      processedValue = value[0];
    }
    
    const jsonString = typeof processedValue === 'string' 
      ? processedValue 
      : JSON.stringify(processedValue, null, 2);
    
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
      title={title}
    >
      <div className="space-y-4">
        {/* Task ID Display */}
        {(() => {
          const displayTaskId = taskId || 
            (typeof details?.task_id === 'string' ? details.task_id : '') || 
            (typeof details?.id === 'string' ? details.id : '');
          
          return displayTaskId && (
            <div className="bg-linear-to-r from-gray-800/50 to-gray-700/30 border border-gray-600/30 rounded-lg px-4 py-3">
              <div className="flex items-center justify-between">
                <div className="flex items-center space-x-3">
                  <div className="w-2 h-2 bg-blue-400 rounded-full animate-pulse"></div>
                  <div>
                    <span className="text-xs font-medium text-gray-400 uppercase tracking-wide block">Task ID</span>
                    <span className="text-sm font-mono text-blue-400 bg-blue-500/10 px-2 py-1 rounded border border-blue-500/20 mt-1 inline-block">
                      {displayTaskId}
                    </span>
                  </div>
                </div>
                <button
                  onClick={() => navigator.clipboard?.writeText(displayTaskId)}
                  className="text-gray-400 hover:text-blue-400 transition-colors duration-200 p-1 rounded hover:bg-blue-500/10"
                  title="Copy Task ID"
                >
                  <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M8 16H6a2 2 0 01-2-2V6a2 2 0 012-2h8a2 2 0 012 2v2m-6 12h8a2 2 0 002-2v-8a2 2 0 00-2-2h-8a2 2 0 00-2 2v8a2 2 0 002 2z" />
                  </svg>
                </button>
              </div>
            </div>
          );
        })()}
        
        {availableKeys.length > 0 && (
          <>
            {/* Tab Navigation */}
            <div className="flex flex-wrap border-b border-white/10">
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

            {/* Tab Content */}
            <div className="mt-4">
              {activeTab && details[activeTab] !== undefined && (
                <>
                  {/* Try custom UI first */}
                  {customKeys.includes(activeTab) 
                    ? renderCustomContent(activeTab, details[activeTab])
                    : renderJsonContent(activeTab, details[activeTab])
                  }
                </>
              )}
            </div>
          </>
        )}
        
        {availableKeys.length === 0 && (
          <div className="text-center text-gray-400 py-8">
            No details available
          </div>
        )}
      </div>
    </Modal>
  );
};

export default TaskDetailsModal;