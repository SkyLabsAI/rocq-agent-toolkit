import React from 'react';
import cn from 'classnames';
import { StatusBadge } from '../statusBadge';

interface TacticObject {
  name: string;
  next_tactic_prediction: string;
  status: "success" | "failure";
  explaination: string;
  [key: string]: unknown; // Additional dynamic properties
}

interface TacticInfoViewerProps {
  tactics: TacticObject[];
  title?: string;
}

const TacticInfoViewer: React.FC<TacticInfoViewerProps> = ({ tactics, title = "Tactic Information" }) => {


  console.warn("TacticInfoViewer rendered with tactics:", tactics);

  if (!tactics || tactics.length === 0) {
    return (
      <div className="text-center text-text py-8">
        No tactic information available
      </div>
    );
  }

  const getStatusColor = (status: "success" | "failure") => {
    return status === "success" 
      ? "bg-green-500/20 text-green-300 border-green-500/30"
      : "bg-red-500/20 text-red-300 border-red-500/30";
  };

  const getStatusBgColor = (status: "success" | "failure") => {
    return status === "success" 
      ? "bg-green-500/5 border-green-500/20"
      : "bg-red-500/5 border-red-500/20";
  };

  // Get all unique additional keys across all tactics (excluding the standard ones)
  const standardKeys = new Set(['name', 'next_tactic_prediction', 'status', 'explaination']);
  const additionalKeys = new Set<string>();
  
  tactics.forEach(tactic => {
    Object.keys(tactic).forEach(key => {
      if (!standardKeys.has(key)) {
        additionalKeys.add(key);
      }
    });
  });

  return (
    <div className="space-y-4">
      {title && (
        <h3 className="text-lg font-semibold text-text mb-4 flex items-center">
          {title}
        </h3>
      )}
      
      {tactics.map((tactic, index) => (
        <div 
          key={index} 
          className={cn(
            "border rounded-lg p-4 transition-all duration-200",
            getStatusBgColor(tactic.status)
          )}
        >
          {/* Header with tactic name and status */}
          <div className="flex items-center justify-between mb-4">
            <div className="flex items-center space-x-3">
              <span className="text-sm font-medium text-text">
                Tactic {index + 1}
              </span>
              <h4 className="text-base font-semibold text-text">
                {tactic.name}
              </h4>
            </div>
            <StatusBadge status={tactic.status} />
          </div>

          {/* Main content grid */}
          <div className="grid grid-cols-1 lg:grid-cols-2 gap-4">
            {/* Next Tactic Prediction */}
            <div className="space-y-2">
              <h5 className="text-sm font-medium text-text">Next Tactic Prediction</h5>
              <div className="bg-elevation-surface border border-elevation-surface-overlay rounded-md p-3">
                <code className="text-sm text-text">
                  {tactic.next_tactic_prediction}
                </code>
              </div>
            </div>

            {/* Explanation */}
            <div className="space-y-2">
              <h5 className="text-sm font-medium text-text">Explanation</h5>
              <div className="bg-elevation-surface border border-elevation-surface-overlay rounded-md p-3">
                <p className="text-sm text-text">
                  {tactic.explaination}
                </p>
              </div>
            </div>
          </div>

          {/* Additional properties */}
          {additionalKeys.size > 0 && (
            <div className="mt-4 pt-4 border-t border-white/10">
              <h5 className="text-sm font-medium text-text mb-3">Additional Information</h5>
              <div className="grid grid-cols-1 md:grid-cols-2 gap-3">
                {Array.from(additionalKeys).map(key => {
                  const value = tactic[key];
                  if (value === undefined || value === null) return null;
                  
                  return (
                    <div key={key} className="bg-elevation-surface border border-elevation-surface-overlay rounded-md p-3">
                      <div className="text-xs font-medium text-text uppercase tracking-wide mb-1">
                        {key.replace(/_/g, ' ')}
                      </div>
                      <div className="text-sm text-text">
                        {typeof value === 'string' ? value : JSON.stringify(value, null, 2)}
                      </div>
                    </div>
                  );
                })}
              </div>
            </div>
          )}
        </div>
      ))}
      
      {/* Summary */}
      <div className="mt-6 p-4 bg-elevation-surface-raised border border-elevation-surface-overlay rounded-lg">
        <div className="flex items-center justify-between text-sm">
          <span className="text-text">Total Tactics:</span>
          <span className="text-text font-medium">{tactics.length}</span>
        </div>
        <div className="flex items-center justify-between text-sm mt-2">
          <span className="text-text">Success Rate:</span>
          <span className="text-text font-medium">
            {((tactics.filter(t => t.status === 'success').length / tactics.length) * 100).toFixed(1)}%
          </span>
        </div>
      </div>
    </div>
  );
};

export default TacticInfoViewer;