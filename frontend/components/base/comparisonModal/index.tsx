import React, { useState, useMemo, useEffect } from 'react';
import Modal from '@/components/base/ui/modal';
import cn from 'classnames';
import TacticInfoViewer, { TacticObject } from '@/components/base/tacticInfo';
import CodeContent from './components/CodeContent';
import JsonContent from './components/JsonContent';
import { useComparisonLogs, ComparisonItem } from './hooks/useComparisonLogs';
import { getTabColorClasses } from './utils/tabColors';
import { ChevronUpIcon } from '@/icons/chevron-up';

interface ComparisonModalProps {
  isOpen: boolean;
  onClose: () => void;
  items: ComparisonItem[];
  taskId: string;
}

const customUIKeys = [
  'cpp_code',
  'cppCode',
  'code',
  'targetContent',
  'lemmaContent',
  'statesContent',
  'tactic_prediction_explanation',
  'tactic_prediction_tactic',
  'tactic',
];

const ComparisonModal: React.FC<ComparisonModalProps> = ({
  isOpen,
  onClose,
  items,
  taskId,
}) => {
  const [activeTab, setActiveTab] = useState('');
  const { taskLogs, loading, error } = useComparisonLogs(isOpen, items);

  // Get all available keys from all fetched logs
  const availableKeys = useMemo(() => {
    const keysSet = new Set<string>();
    Object.values(taskLogs).forEach(logs => {
      if (logs && typeof logs === 'object') {
        Object.keys(logs).forEach(key => keysSet.add(key));
      }
    });
    return Array.from(keysSet).sort();
  }, [taskLogs]);

  const customKeys = useMemo(
    () => availableKeys.filter(key => customUIKeys.includes(key)),
    [availableKeys]
  );
  const jsonKeys = useMemo(
    () => availableKeys.filter(key => !customUIKeys.includes(key)),
    [availableKeys]
  );

  // Reset active tab when details change
  useEffect(() => {
    if (availableKeys.length > 0) {
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
    if (key === 'tactic' && Array.isArray(value)) {
      return (
        <TacticInfoViewer
          tactics={value as TacticObject[]}
          title='Tactic Information'
        />
      );
    }

    let stringValues: string[];
    if (Array.isArray(value)) {
      stringValues = value.filter(
        (item): item is string => typeof item === 'string'
      );
    } else if (typeof value === 'string') {
      stringValues = [value];
    } else {
      return null;
    }
    if (stringValues.length === 0) return null;
    return <CodeContent keyName={key} values={stringValues} />;
  };

  // Helper function to render JSON content
  const renderJsonContent = (key: string, value: unknown) => {
    if (
      key !== 'tactic_prediction_explanation' &&
      key !== 'tactic_prediction_tactic' &&
      key !== 'tactic' &&
      Array.isArray(value)
    ) {
      const stringValues = value.filter(
        (item): item is string => typeof item === 'string'
      );
      if (stringValues.length > 0) {
        return (
          <div className='space-y-4'>
            {stringValues.map((str, index) => (
              <div
                key={index}
                className='bg-elevation-surface border border-elevation-surface-overlay rounded-lg p-4 max-h-96 overflow-auto'
              >
                <div className='text-text mb-2'>Item {index + 1}</div>
                <pre className='text-sm text-text whitespace-pre-wrap font-mono'>
                  {str}
                </pre>
              </div>
            ))}
          </div>
        );
      }
    }
    return <JsonContent value={value} />;
  };

  return (
    <Modal
      isOpen={isOpen}
      onClose={onClose}
      title={`Compare Task: ${taskId}`}
      size='full'
    >
      <div className='space-y-4 h-full flex flex-col'>
        {/* Loading State */}
        {loading && (
          <div className='flex-1 flex items-center justify-center'>
            <div className='text-center'>
              <div className='animate-spin rounded-full h-8 w-8 border-b-2 border-blue-400 mx-auto mb-4'></div>
              <p className='text-text'>Loading comparison data...</p>
            </div>
          </div>
        )}
        {/* Error State */}
        {error && !loading && (
          <div className='flex-1 flex items-center justify-center'>
            <div className='text-center text-text-danger'>
              <p>Error: {error}</p>
            </div>
          </div>
        )}
        {/* Content */}
        {!loading && !error && availableKeys.length > 0 && (
          <>
            {/* Tab Navigation */}
            <div className='flex flex-wrap border-b border-elevation-surface-overlay shrink-0'>
              {availableKeys.map(key => (
                <button
                  key={key}
                  onClick={() => setActiveTab(key)}
                  className={cn(
                    'px-4 py-2 text-sm font-medium border-b-2 transition-colors duration-200',
                    getTabColorClasses(key, activeTab === key)
                  )}
                >
                  {key}
                </button>
              ))}
            </div>
            {/* Comparison Content */}
            <div className='flex-1 overflow-hidden'>
              {activeTab && (
                <div className='h-full overflow-y-auto'>
                  <div className='space-y-4'>
                    {items.map((item, index) => {
                      const value = getTaskValue(index, activeTab);
                      const hasData = value !== undefined && value !== null;
                      return (
                        <ComparisonItemCard
                          key={index}
                          item={item}
                          hasData={hasData}
                          value={value}
                          activeTab={activeTab}
                          customKeys={customKeys}
                          renderCustomContent={renderCustomContent}
                          renderJsonContent={renderJsonContent}
                        />
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
          <div className='text-center text-text py-8 flex-1 flex items-center justify-center'>
            No comparable data available
          </div>
        )}
      </div>
    </Modal>
  );
};

export default ComparisonModal;

interface ComparisonItemCardProps {
  item: any;
  hasData: boolean;
  value: unknown;
  activeTab: string;
  customKeys: string[];
  renderCustomContent: (key: string, value: unknown) => React.ReactNode;
  renderJsonContent: (key: string, value: unknown) => React.ReactNode;
}

const ComparisonItemCard: React.FC<ComparisonItemCardProps> = ({
  item,
  hasData,
  value,
  activeTab,
  customKeys,
  renderCustomContent,
  renderJsonContent,
}) => {
  const [isOpen, setIsOpen] = useState(false);

  return (
    <div
      className='border border-elevation-surface-overlay rounded-lg bg-elevation-surface-raised p-4'
      onClick={() => setIsOpen(!isOpen)}
    >
      <div className='flex items-center justify-between mb-4 shrink-0'>
        <div className='flex gap-2 items-center'>
          <ChevronUpIcon
            className={cn('size-6 text-text', { 'rotate-180': isOpen })}
          />
          <div className='flex flex-col text-text'>
            <h4 className='text-sm font-medium truncate' title={item.label}>
              {item.label}
            </h4>
            {item.task && (
              <span
                className='text-xs text-text-disabled font-mono'
                title={item.task.run_id}
              >
                Run: {item.task.run_id}
              </span>
            )}
          </div>
        </div>
      </div>
      {isOpen && (
        <div className='overflow-auto'>
          {!hasData ? (
            <div className='text-sm text-text-disabled italic text-center py-8'>
              {!item.task ? 'Task not present' : 'No data for this key'}
            </div>
          ) : (
            <>
              {customKeys.includes(activeTab)
                ? renderCustomContent(activeTab, value)
                : renderJsonContent(activeTab, value)}
            </>
          )}
        </div>
      )}
    </div>
  );
};
