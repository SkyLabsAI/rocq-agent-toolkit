import React from 'react';

interface ButtonProps extends React.ButtonHTMLAttributes<HTMLButtonElement> {
  leftIcon?: React.ReactNode;
  rightIcon?: React.ReactNode;
  leftDivider?: boolean;
  rightDivider?: boolean;
  variant?: 'default' | 'ghost';
  children: React.ReactNode;
}

export function Button({ 
  leftIcon,
  rightIcon,
  leftDivider = false,
  rightDivider = false,
  variant = 'default',
  children,
  className = '',
  ...props 
}: ButtonProps) {
  const baseClasses = variant === 'default' 
    ? 'bg-[#393d46] relative rounded-[4px] shrink-0'
    : 'relative rounded-[4px] shrink-0';

  const renderDivider = () => (
    <div className="flex h-[calc(1px*((var(--transform-inner-width)*1)+(var(--transform-inner-height)*0)))] items-center justify-center relative shrink-0 w-[calc(1px*((var(--transform-inner-height)*1)+(var(--transform-inner-width)*0)))]" style={{ "--transform-inner-width": "18", "--transform-inner-height": "0" } as React.CSSProperties}>
      <div className="flex-none rotate-[90deg]">
        <div className="h-0 relative w-[18px]">
          <div className="absolute bottom-0 left-0 right-0 top-[-1px]">
            <svg className="block size-full" fill="none" preserveAspectRatio="none" viewBox="0 0 18 1">
              <line stroke="var(--stroke-0, #525865)" x2="18" y1="0.5" y2="0.5" />
            </svg>
          </div>
        </div>
      </div>
    </div>
  );

  return (
    <button className={`${baseClasses} ${className}`} {...props}>
      <div className="box-border content-stretch flex gap-[12px] items-center overflow-clip px-[12px] py-[8px] relative rounded-[inherit]">
        {leftIcon && (
          <div className="content-stretch flex gap-[6px] items-center relative shrink-0">
            {leftIcon}
          </div>
        )}
        
        {leftDivider && renderDivider()}
        
        <p className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-[#e1e2e3] text-[14px] text-nowrap whitespace-pre" style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}>
          {children}
        </p>
        
        {rightDivider && renderDivider()}
        
        {rightIcon && (
          <div className="flex items-center justify-center relative shrink-0">
            {rightIcon}
          </div>
        )}
      </div>
      {variant === 'default' && (
        <div aria-hidden="true" className="absolute border border-[#525865] border-solid inset-0 pointer-events-none rounded-[4px] shadow-[0px_1px_4px_0px_rgba(0,0,0,0.08)]" />
      )}
    </button>
  );
}


export default Button;