import React from 'react';
import { Prism as SyntaxHighlighter } from 'react-syntax-highlighter';
import { vscDarkPlus } from 'react-syntax-highlighter/dist/esm/styles/prism';

interface CodeViewerProps {
  code: string;
  language: string;
  filename?: string;
}

const CodeViewer: React.FC<CodeViewerProps> = ({ code, language, filename }) => {
  // Map language names to syntax highlighter compatible names
  const getLanguage = (lang: string) => {
    switch (lang.toLowerCase()) {
      case 'cpp':
      case 'c++':
        return 'cpp';
      case 'text':
      case 'txt':
        return 'text';
      default:
        return lang.toLowerCase();
    }
  };

  return (
    <div className="bg-slate-800 border border-white/10 rounded-lg overflow-hidden">
      {filename && (
        <div className="bg-slate-700 px-4 py-2 border-b border-white/10">
          <span className="text-sm font-medium text-gray-300">{filename}</span>
          <span className="text-xs text-gray-400 ml-2">({language})</span>
        </div>
      )}
      <div className="overflow-auto max-h-[60vh]">
        <SyntaxHighlighter
          language={getLanguage(language)}
          style={vscDarkPlus}
          customStyle={{
            margin: 0,
            padding: '1rem',
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
          {code}
        </SyntaxHighlighter>
      </div>
    </div>
  );
};

export default CodeViewer;