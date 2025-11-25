import React from 'react';
import { Prism as SyntaxHighlighter } from 'react-syntax-highlighter';
import { vscDarkPlus } from 'react-syntax-highlighter/dist/esm/styles/prism';

interface TacticStepsViewerProps {
  steps: string[];
  type: 'explanation' | 'tactic';
  title: string;
}

const TacticStepsViewer: React.FC<TacticStepsViewerProps> = ({ steps, type, title }) => {
  const getStepIcon = (index: number) => {
    return (
      <div className={`shrink-0 w-8 h-8 rounded-full flex items-center justify-center text-sm font-semibold ${
        type === 'explanation' 
          ? 'bg-blue-500/20 text-text-information border border-blue-400/30' 
          : 'bg-green-500/20 text-text-success border border-green-400/30'
      }`}>
        {index + 1}
      </div>
    );
  };

  const getHeaderColor = () => {
    return type === 'explanation' 
      ? 'bg-blue-500/10 border-blue-400/30 text-blue-300' 
      : 'bg-green-500/10 border-green-400/30 text-green-300';
  };

  return (
    <div className="bg-slate-800 border border-elevation-surface-overlay rounded-lg overflow-hidden">
      {/* Header */}
      <div className={`px-4 py-3 border-b border-elevation-surface-overlay ${getHeaderColor()}`}>
        <div className="flex items-center gap-2">
          {type === 'explanation' ? (
            <svg className="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} 
                d="M13 16h-1v-4h-1m1-4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
            </svg>
          ) : (
            <svg className="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} 
                d="M10 20l4-16m4 4l4 4-4 4M6 16l-4-4 4-4" />
            </svg>
          )}
          <span className="font-medium">{title}</span>
          <span className="text-xs opacity-75">({steps.length} steps)</span>
        </div>
      </div>

      {/* Steps Content */}
      <div className="p-4 space-y-4 max-h-[60vh] overflow-auto">
        {steps.map((step, index) => (
          <div key={index} className="flex gap-3">
            {getStepIcon(index)}
            <div className="flex-1 min-w-0">
              {type === 'explanation' ? (
                // Explanation steps - render as formatted text
                <div className="bg-gray-900/50 border border-white/10 rounded-lg p-3">
                  <p className="text-sm text-gray-300 leading-relaxed whitespace-pre-wrap">
                    {step}
                  </p>
                </div>
              ) : (
                // Tactic steps - render as syntax-highlighted code
                <div className="bg-gray-900/50 border border-white/10 rounded-lg overflow-hidden">
                  <SyntaxHighlighter
                    language="coq"
                    style={vscDarkPlus}
                    customStyle={{
                      margin: 0,
                      padding: '0.75rem',
                      background: 'transparent',
                      fontSize: '0.875rem',
                      lineHeight: '1.5',
                    }}
                    codeTagProps={{
                      style: {
                        fontFamily: 'ui-monospace, SFMono-Regular, "SF Mono", Consolas, "Liberation Mono", Menlo, monospace',
                      }
                    }}
                  >
                    {step}
                  </SyntaxHighlighter>
                </div>
              )}
            </div>
          </div>
        ))}
        
        {steps.length === 0 && (
          <div className="text-center py-8 text-gray-400">
            <svg className="w-12 h-12 mx-auto mb-4 opacity-50" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} 
                d="M9 12h6m-6 4h6m2 5H7a2 2 0 01-2-2V5a2 2 0 012-2h5.586a1 1 0 01.707.293l5.414 5.414a1 1 0 01.293.707V19a2 2 0 01-2 2z" />
            </svg>
            <p>No {type} steps available</p>
          </div>
        )}
      </div>
    </div>
  );
};

export default TacticStepsViewer;