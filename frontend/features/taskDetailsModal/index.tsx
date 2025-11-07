import React, { useState } from 'react';
import Modal from '@/components/base/modal';
import CodeViewer from '@/components/base/codeViewer';
import cn from 'classnames';

interface TaskDetailsModalProps {
  isOpen: boolean;
  onClose: () => void;
  details: Record<string, unknown> | null;
  title?: string;
}

const TaskDetailsModal: React.FC<TaskDetailsModalProps> = ({ isOpen, onClose, details, title = 'Task Details' }) => {
  const [activeTab, setActiveTab] = useState<string>('');

  // Define which keys should have custom UI
  const customUIKeys = React.useMemo(() => 
    ['cpp_code', 'cppCode', 'code', 'targetContent', 'lemmaContent', 'statesContent'], []
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
    if (typeof value !== 'string') return null;

    const lowerKey = key.toLowerCase();
    
    if (lowerKey.includes('cpp') || lowerKey.includes('code')) {
      return (
        <CodeViewer
          code={value}
          language="cpp"
          filename={`${key}.cpp`}
        />
      );
    }
    
    if (lowerKey.includes('target') || lowerKey.includes('lemma') || lowerKey.includes('states')) {
      return (
        <CodeViewer
          code={value}
          language="text"
          filename={`${key}.txt`}
        />
      );
    }
    
    return null;
  };

  // Helper function to render JSON content
  const renderJsonContent = (key: string, value: unknown) => {
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