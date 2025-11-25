import React, { useState } from 'react';
import Modal from '@/components/base/modal';
import CodeViewer from '@/components/base/codeViewer';
import TacticStepsViewer from '@/components/base/tacticSteps';
import TacticInfoViewer, { TacticObject } from '@/components/base/tacticInfo';
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
    ['cpp_code', 'cppCode', 'code', 'targetContent', 'lemmaContent', 'statesContent', 'tactic_prediction_explanation', 'tactic_prediction_tactic', 'tactic'], []
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
    // Handle new tactic_info array with structured tactic objects
    if (key === 'tactic' && Array.isArray(value)) {
      return (
        <TacticInfoViewer
          tactics={value as TacticObject[]}
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
    if (key !== 'tactic_prediction_explanation' && key !== 'tactic_prediction_tactic' && key !== 'tactic' && Array.isArray(value)) {
      const stringValues = value.filter((item): item is string => typeof item === 'string');
      if (stringValues.length > 0) {
        return (
          <div className="space-y-4">
            {stringValues.map((str, index) => (
              <div key={index} className="bg-gray-900/50 border border-white/10 rounded-lg p-4 max-h-96 overflow-auto">
                <div className="text-xs text-gray-400 mb-2">Item {index + 1}</div>
                <pre className="text-sm text-text whitespace-pre-wrap font-mono">
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
        <pre className="text-sm text-text whitespace-pre-wrap font-mono">
          {jsonString}
        </pre>
      </div>
    );
  };

  // Helper function to get tab color based on key
  const getTabColor = (key: string) => {
    const lowerKey = key.toLowerCase();
    if (key === 'tactic') return 'purple';
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
      return  'border-text-information text-text-information';
    }
    return 'border-transparent text-gray-400 hover:text-gray-300';
  };

  return (
    <Modal
      isOpen={isOpen}
      onClose={onClose}
      title={title}
      size='full'
    >
      <div className="space-y-4">
        {/* Task ID Display */}
       
        
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