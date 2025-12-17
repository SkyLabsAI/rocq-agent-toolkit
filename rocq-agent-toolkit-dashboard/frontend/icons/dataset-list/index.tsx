import React from 'react';

export const DataSetListIcon: React.FC<{ className?: string }> = ({
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
        d='M2.417 2.416h2.417v1.208H2.417V2.416Zm7.25 9.063h2.417v1.208H9.667v-1.208ZM1.208 5.437H4.23v1.208H1.21V5.437Zm4.23 0H7.25v1.208H5.438V5.437Zm3.02 0h3.626v1.208H8.459V5.437Zm-6.041 3.02h3.625v1.209H2.417V8.458Zm4.833 0h1.813v1.209H7.25V8.458Zm3.021 0h3.02v1.209h-3.02V8.458Zm-4.23-6.041h7.25v1.208h-7.25V2.416Zm-4.833 9.063h7.25v1.208h-7.25v-1.208Z'
      />
    </svg>
  );
};
