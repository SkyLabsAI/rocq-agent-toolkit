import ChevronUpSmallIcon from "@/icons/chevron-up-small";
import { SortIcon } from "@/icons/sort/sort";

export const FilterFieldsButton = () => (
  <div className='bg-[#393d46] relative rounded-[4px] shrink-0'>
    <div className='box-border content-stretch flex gap-[12px] items-center overflow-clip px-[12px] py-[8px] relative rounded-[inherit]'>
      <div className='content-stretch flex gap-[6px] items-center relative shrink-0'>
        <SortIcon />
        <p
          className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-[#cecfd2] text-[14px] text-nowrap whitespace-pre"
          style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
        >
          Filter Fields
        </p>
      </div>
      <div
        className='flex h-[calc(1px*((var(--transform-inner-width)*1)+(var(--transform-inner-height)*0)))] items-center justify-center relative shrink-0 w-[calc(1px*((var(--transform-inner-height)*1)+(var(--transform-inner-width)*0)))]'
        style={
          {
            '--transform-inner-width': '18',
            '--transform-inner-height': '0',
          } as React.CSSProperties
        }
      >
        <div className='flex-none rotate-[90deg]'>
          <div className='h-0 relative w-[18px]'>
            <div
              className=' bottom-0 left-0 right-0 top-[-1px]'
              style={
                { '--stroke-0': 'rgba(82, 88, 101, 1)' } as React.CSSProperties
              }
            >
              <svg
                className='block size-full'
                fill='none'
                preserveAspectRatio='none'
                viewBox='0 0 18 1'
              >
                <line
                  id='Line 10'
                  stroke='var(--stroke-0, #525865)'
                  x2='18'
                  y1='0.5'
                  y2='0.5'
                />
              </svg>
            </div>
          </div>
        </div>
      </div>
      <div className='flex items-center justify-center relative shrink-0'>
        <div className='flex-none scale-y-[-100%]'>
          <ChevronUpSmallIcon />
        </div>
      </div>
    </div>
    <div
      aria-hidden='true'
      className=' border border-[#525865] border-solid inset-0 pointer-events-none rounded-[4px] shadow-[0px_1px_4px_0px_rgba(0,0,0,0.08)]'
    />
  </div>
);

