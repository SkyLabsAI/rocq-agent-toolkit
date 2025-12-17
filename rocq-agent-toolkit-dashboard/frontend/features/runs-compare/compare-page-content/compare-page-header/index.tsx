import { Link } from 'react-router-dom';

import { ChevronUpIcon } from '@/icons/chevron-up';

export const CompareRunsHeader = ({
  title,
  secondary,
}: {
  title: string;
  secondary?: string;
}) => (
  <div className=' bg-elevation-surface-raised box-border content-stretch flex items-center justify-between left-0 overflow-clip px-[24px] py-[16px] top-[48px] w-full rounded-lg'>
    <div className='basis-0 content-stretch flex grow items-center justify-between min-h-px min-w-px relative shrink-0'>
      <div className='content-stretch flex gap-[11px] items-center relative shrink-0'>
        <div
          className='flex h-[calc(1px*((var(--transform-inner-width)*1)+(var(--transform-inner-height)*0)))] items-center justify-center relative shrink-0 w-[calc(1px*((var(--transform-inner-height)*1)+(var(--transform-inner-width)*0)))]'
          style={
            {
              '--transform-inner-width': '24',
              '--transform-inner-height': '24',
            } as React.CSSProperties
          }
        >
          <Link to={'/'}>
            <div className='flex justify-center items-center rotate-[270deg] scale-y-[-100%] w-[38px] h-[38px] hover:bg-background-neutral-hovered rounded-lg'>
              <ChevronUpIcon className='size-6 m-auto' />
            </div>
          </Link>
        </div>
        <div className='content-stretch flex flex-col gap-[4px] h-[48px] items-start leading-[20px] relative shrink-0 text-[14px] w-[198px]'>
          <p
            className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold relative shrink-0 text-text w-full"
            style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
          >
            {/* Compare Runs */}
            {title}
          </p>
          <p
            className="font-['Noto_Sans:Regular',sans-serif] font-normal relative shrink-0 text-text-disabled w-full whitespace-nowrap"
            style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
          >
            {secondary}
          </p>
        </div>
      </div>
    </div>
  </div>
);
