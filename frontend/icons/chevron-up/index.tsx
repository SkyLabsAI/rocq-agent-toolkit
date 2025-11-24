import React from 'react';

export const ChevronUpIcon: React.FC<{ className?: string }> = ({ className }) => {
  return (
    <svg
      viewBox="0 0 18 18"
      width="18px"
      height="18px"
      fill="currentColor"
      className={className}

    >
      <path
        fill="currentColor"
        d="M5.558 6.442 9 9.877l3.443-3.435L13.5 7.5 9 12 4.5 7.5l1.058-1.058Z"
      />
    </svg>
  );
};
