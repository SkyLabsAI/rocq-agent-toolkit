import React from 'react';

export const PinOutlineIcon: React.FC<{ className?: string }> = ({
  className,
}) => {
  return (
    <svg
      width='20'
      height='20'
      fill='currentColor'
      viewBox='0 0 20 20'
      className={className}
    >
      <path
        fill='currentColor'
        fillOpacity='.25'
        d='M13.333 10V3.334h.834V1.667H5.833v1.667h.834V10L5 11.667v1.667h4.333v5h1.334v-5H15v-1.667L13.333 10Zm-6 1.667 1-1V3.334h3.334v7.333l1 1H7.333Z'
      />
    </svg>
  );
};
