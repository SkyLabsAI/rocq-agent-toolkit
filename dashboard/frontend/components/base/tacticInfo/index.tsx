import React from 'react';
import cn from 'classnames';
import { StatusBadge } from '../statusBadge';

export interface TacticObject {
  goal: string;
  tactic_prediction_tactic: string;
  status?: 'success' | 'failure' | "not found";
  tactic_prediction_explanation: string;
  [key: string]: unknown; // Additional dynamic properties
}

interface TacticInfoViewerProps {
  tactics: TacticObject[];
  title?: string;
}

const TacticInfoViewer: React.FC<TacticInfoViewerProps> = ({
  tactics,
  title = 'Tactic Information',
}) => {
  console.warn('TacticInfoViewer rendered with tactics:', tactics);

  if (!tactics || tactics.length === 0) {
    return (
      <div className='text-center text-text py-8'>
        No tactic information available
      </div>
    );
  }

  const getStatusBgColor = (status: 'success' | 'failure' | "not found") => {
    const lower = status.toLowerCase();
    if (lower === 'success') {
      return 'bg-text-success';
    } else if (lower === 'not found') {
      return 'bg-gray-300 border-gray-300';
    } else {
      return 'bg-text-danger border-text-danger';
    }
  };

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
        <div
          key={index}
          className={cn(
            'border rounded-lg pb-0 px-0 pt-0 transition-all duration-200 bg-elevation-surface-raised border-elevation-surface-overlay overflow-hidden',
            
          )}
        >
          {/* Header with tactic name and status */}
           <div className={'h-2 w-full mb-4 '+ getStatusBgColor(tactic.status || "not found")}/>
          <div className='flex items-center justify-between mb-4 px-4'>
            <div className='flex items-center space-x-3'>
              <span className='text-sm font-medium text-text'>
                Tactic {index + 1}
              </span>
              <h4 className='text-base font-semibold text-text'>
                {tactic.goal}
              </h4>
            </div>
            <StatusBadge status={tactic.status || "Not found"} />
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
              <h5 className='text-sm font-medium text-text mb-3'>
                Additional Information
              </h5>
              <div className='grid grid-cols-1 md:grid-cols-2 gap-3'>
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
          )}
        </div>
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
              (tactics.filter(t => t.status?.toLowerCase() === 'success').length /
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
