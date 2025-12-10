import React from 'react';
import CodeViewer from '@/components/base/codeViewer';

interface CodeContentProps {
  keyName: string;
  values: string[];
}

const CodeContent: React.FC<CodeContentProps> = ({ keyName, values }) => {
  const lowerKey = keyName.toLowerCase();
  const language =
    lowerKey.includes('cpp') || lowerKey.includes('code') ? 'cpp' : 'text';
  const ext = language === 'cpp' ? 'cpp' : 'txt';

  return (
    <div className='space-y-4'>
      {values.map((code, index) => (
        <CodeViewer
          key={index}
          code={code}
          language={language}
          filename={`${keyName}_${index + 1}.${ext}`}
        />
      ))}
    </div>
  );
};

export default CodeContent;
