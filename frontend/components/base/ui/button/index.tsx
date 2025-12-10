import React from 'react';

interface ButtonProps extends React.ButtonHTMLAttributes<HTMLButtonElement> {
  leftIcon?: React.ReactNode;
  rightIcon?: React.ReactNode;
  leftDivider?: boolean;
  rightDivider?: boolean;
  variant?: 'default' | 'ghost' | 'danger' | 'outline';
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
  const getBaseClasses = () => {
    const baseStyles =
      'relative rounded-[4px] shrink-0 cursor-pointer overflow-hidden';
    const textStyles =
      'font-["Noto_Sans"] text-[14px] font-normal leading-5 text-text';

    switch (variant) {
      case 'default':
        return `${baseStyles} ${textStyles} bg-background-accent-gray-subtlest border border-background-accent-gray-subtler shadow-[0px_1px_4px_0px_rgba(0,0,0,0.08)]`;
      case 'outline':
        return `${baseStyles} ${textStyles}  border border-background-accent-gray-subtler shadow-[0px_1px_4px_0px_rgba(0,0,0,0.08)]`;
      case 'danger':
        return `${baseStyles} ${textStyles} bg-background-danger border text-text-danger border-background-danger-hovered`;
      case 'ghost':
        return `${baseStyles} ${textStyles} border border-transparent hover:bg-background-neutral-hovered`;
      default:
        return `${baseStyles} ${textStyles} border border-transparent`;
    }
  };

  const baseClasses = getBaseClasses();

  const renderDivider = () => <div className='flex h-4 w-px bg-border-bold' />;

  return (
    <button className={`${baseClasses} ${className}`} {...props}>
      <div className='box-border content-stretch flex gap-1.5 items-center overflow-clip px-3 py-2 relative rounded-[inherit]'>
        {leftIcon && (
          <div className='content-stretch flex gap-1.5 items-center relative shrink-0'>
            {leftIcon}
          </div>
        )}

        {leftDivider && renderDivider()}

        <span className='font-noto-sans text-sm font-normal leading-5 whitespace-nowrap'>
          {children}
        </span>

        {rightDivider && renderDivider()}

        {rightIcon && (
          <div className='flex items-center justify-center relative shrink-0'>
            {rightIcon}
          </div>
        )}
      </div>
    </button>
  );
}

export default Button;
