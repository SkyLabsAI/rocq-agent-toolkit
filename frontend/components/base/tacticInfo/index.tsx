import cn from 'classnames';
import { useState } from 'react';

import { ChevronUpIcon } from '@/icons/chevron-up';

import { StatusBadge } from '../statusBadge';

export interface TacticObject {
  goal: string;
  tactic_prediction_tactic: string;
  status?: 'success' | 'failure' | 'not found';
  tactic_prediction_explanation: string;
  [key: string]: unknown; // Additional dynamic properties
}

interface TacticItemProps {
  tactic: TacticObject;
  index: number;
  additionalKeys: Set<string>;
}

const TacticItem: React.FC<TacticItemProps> = ({
  tactic,
  index,
  additionalKeys,
}) => {
  const [isAdditionalInfoOpen, setIsAdditionalInfoOpen] = useState(false);

  const getStatusBgColor = (status: 'success' | 'failure' | 'not found') => {
    const lower = status.toLowerCase();
    if (lower === 'success') {
      return 'bg-text-success';
    } else if (lower === 'not found') {
      return 'bg-gray-300 border-gray-300';
    } else {
      return 'bg-text-danger border-text-danger';
    }
  };

  return (
    <div
      className={cn(
        'border rounded-lg pb-0 px-0 pt-0 transition-all duration-200 bg-elevation-surface-raised border-elevation-surface-overlay overflow-hidden'
      )}
    >
      {/* Header with tactic name and status */}
      <div
        className={
          'h-1 w-full mb-4 ' + getStatusBgColor(tactic.status || 'not found')
        }
      />
      <div className='flex items-center justify-between mb-4 px-4'>
        <div className='flex items-center space-x-3'>
          <span className='text-sm font-medium text-text'>
            Tactic {index + 1}
          </span>
          <h4 className='text-base font-semibold text-text'>{tactic.goal}</h4>
        </div>
        <StatusBadge status={tactic.status || 'Not found'} />
      </div>

      {/* Main content grid */}
      <div className='grid grid-cols-1 lg:grid-cols-2 gap-4 px-4'>
        {/* Next Tactic Prediction */}
        {tactic.tactic_prediction_tactic && (
          <div className='space-y-2'>
            <h5 className='text-sm font-medium text-text whitespace-pre-line'>
              Next Tactic Prediction
            </h5>
            <div className='bg-elevation-surface border border-elevation-surface-overlay rounded-md p-3'>
              <pre className='text-sm text-text text-wrap'>
                {tactic.tactic_prediction_tactic}
              </pre>
            </div>
          </div>
        )}

        {/* Explanation */}
        {tactic.tactic_prediction_explanation && (
          <div className='space-y-2'>
            <h5 className='text-sm font-medium text-text'>Explanation</h5>
            <div className='bg-elevation-surface border border-elevation-surface-overlay rounded-md p-3'>
              <p className='text-sm text-text'>
                {tactic.tactic_prediction_explanation}
              </p>
            </div>
          </div>
        )}
      </div>

      {/* Additional properties */}
      {additionalKeys.size > 0 && (
        <div className='mt-4 pt-4 border-t border-white/10 px-4 pb-4'>
          <div
            className='flex gap-1 items-center mb-3 cursor-pointer select-none'
            onClick={e => {
              setIsAdditionalInfoOpen(!isAdditionalInfoOpen);
              e.stopPropagation();
            }}
          >
            <ChevronUpIcon
              className={cn(
                'transition-transform duration-200 ease-in-out size-5 text-text',
                { 'rotate-180': isAdditionalInfoOpen }
              )}
            />
            <h5 className='text-sm font-medium text-text'>
              Additional Information
            </h5>
          </div>
          <div
            className={cn(
              'overflow-hidden transition-all duration-300 ease-in-out',
              isAdditionalInfoOpen ? ' opacity-100' : 'max-h-0 opacity-0'
            )}
          >
            <div className='grid grid-cols-1 md:grid-cols-2 gap-3 pb-1'>
              {Array.from(additionalKeys).map(key => {
                const value = tactic[key];
                if (value === undefined || value === null) return null;

                return (
                  <div
                    key={key}
                    className='bg-elevation-surface border border-elevation-surface-overlay rounded-md p-3'
                  >
                    <div className='text-xs font-medium text-text uppercase tracking-wide mb-1'>
                      {key.replace(/_/g, ' ')}
                    </div>
                    <pre className='text-sm text-text'>
                      {typeof value === 'string'
                        ? value
                        : JSON.stringify(value, null, 2)}
                    </pre>
                  </div>
                );
              })}
            </div>
          </div>
        </div>
      )}
    </div>
  );
};

interface TacticInfoViewerProps {
  tactics: TacticObject[];
  title?: string;
}

const TacticInfoViewer: React.FC<TacticInfoViewerProps> = ({
  tactics,
  title = 'Tactic Information',
}) => {
  if (!tactics || tactics.length === 0) {
    return (
      <div className='text-center text-text py-8'>
        No tactic information available
      </div>
    );
  }

  // Get all unique additional keys across all tactics (excluding the standard ones)
  const standardKeys = new Set([
    'name',
    'tactic_prediction_tactic',
    'status',
    'tactic_prediction_explanation',
  ]);
  const additionalKeys = new Set<string>();

  tactics.forEach(tactic => {
    Object.keys(tactic).forEach(key => {
      if (!standardKeys.has(key)) {
        additionalKeys.add(key);
      }
    });
  });

  return (
    <div className='space-y-4'>
      {title && (
        <h3 className='text-lg font-semibold text-text mb-4 flex items-center'>
          {title}
        </h3>
      )}

      {tactics.map((tactic, index) => (
        <TacticItem
          key={index}
          tactic={tactic}
          index={index}
          additionalKeys={additionalKeys}
        />
      ))}

      {/* Summary */}
      <div className='mt-6 p-4 bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg'>
        <div className='flex items-center justify-between text-sm'>
          <span className='text-text'>Total Tactics:</span>
          <span className='text-text font-medium'>{tactics.length}</span>
        </div>
        <div className='flex items-center justify-between text-sm mt-2'>
          <span className='text-text'>Success Rate:</span>
          <span className='text-text font-medium'>
            {(
              (tactics.filter(t => t.status?.toLowerCase() === 'success')
                .length /
                tactics.length) *
              100
            ).toFixed(1)}
            %
          </span>
        </div>
      </div>
    </div>
  );
};

export default TacticInfoViewer;
