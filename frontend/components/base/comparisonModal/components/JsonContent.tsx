import React from 'react';

interface JsonContentProps {
  value: unknown;
}

const JsonContent: React.FC<JsonContentProps> = ({ value }) => {
  const jsonString = typeof value === 'string' 
    ? value 
    : JSON.stringify(value, null, 2);

  return (
    <div className="bg-elevation-surface-raised border border-elevation-surface-raised rounded-lg p-4 max-h-96 overflow-auto">
      <pre className="text-sm text-text whitespace-pre-wrap font-mono">
        {jsonString}
      </pre>
    </div>
  );
};

export default JsonContent;
