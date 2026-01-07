import React from 'react';

export const ProjectListIcon: React.FC<{ className?: string }> = ({
  className,
}) => {
  return (
    <svg
      width='15'
      height='15'
      fill='none'
      viewBox='0 0 15 15'
      className={className}
    >
      <path
        fill='currentColor'
        d='M2.5 2.5h10v10h-10v-10Zm1 1v8h8v-8h-8Zm1 1h6v1h-6v-1Zm0 2h6v1h-6v-1Zm0 2h4v1h-4v-1Z'
      />
    </svg>
  );
};
