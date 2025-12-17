import React from 'react';

export const PinIcon: React.FC<{ className?: string }> = ({ className }) => {
  return (
    <svg
      width='20px'
      height='20px'
      fill='currentColor'
      viewBox='0 0 20 20'
      className={className ? `${className} icon-center` : 'icon-center'}
    >
      <path
        fill='currentColor'
        d='M13.333 8.833V2.167h.834V.5H5.833v1.667h.834v6.666L5 10.5v1.667h4.333v5h1.334v-5H15V10.5l-1.667-1.667Z'
      />
    </svg>
  );
};
