'use client';
import Link from 'next/link';

import ThemeSwitcher from '@/components/theme-switcher';
import { LogoIcon } from '@/icons/logo/logo';

const Layout = ({
  title,
  children,
}: {
  title: string;
  children: React.ReactNode;
}) => {
  return (
    <div className='min-h-screen bg-elevation-surface-sunken text-text flex flex-col'>
      {/* Header */}
      <div className='justify-center border-b border-elevation-surface-overlay bg-elevation-surface'>
        <div className='flex items-center justify-between gap-4 backdrop-blur-sm  px-10 py-[10px]'>
          <div className='flex items-center'>
            <Link href={'/'}>
              <div
                className='flex items-center'
                onClick={() => window.location.reload()}
              >
                <LogoIcon />
                <h1 className="ml-2.5 text-text font-['Noto_Sans'] text-base font-normal text-[16px] leading-[normal]">
                  Skylabs AI
                </h1>
              </div>
            </Link>
            <div className='h-7 w-px mx-4.5 bg-background-accent-gray-subtlest'></div>
            <h1 className="text-text-subtlest font-['Noto_Sans'] text-base text-[16px] font-normal leading-[normal]">
              {title}
            </h1>
          </div>
          <ThemeSwitcher className='mr-2 relative right-2' />
        </div>
      </div>

      <main className='main' role='main'>
        <div className='px-10  mt-19 pb-19'>{children}</div>
      </main>
    </div>
  );
};

export default Layout;
