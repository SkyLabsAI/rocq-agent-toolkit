import React from 'react';

export const SortIcon: React.FC<{ className?: string }> = ({ className }) => {
  return (
    <svg width='18' height='18' fill='none' className={className}>
      <path
        fill='currentColor'
        d='m13.5 15.75-3-3h2.25v-7.5H10.5l3-3 3 3h-2.25v7.5h2.25m-15 1.5v-1.5H9v1.5m-7.5-4.5v-1.5h5.25v1.5M1.5 5.25v-1.5h3v1.5h-3Z'
      />
    </svg>
  );
};
