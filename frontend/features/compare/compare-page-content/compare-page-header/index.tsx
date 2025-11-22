import { ChevronUpIcon } from "@/icons/chevron-up";
import Link from "next/link";

export const CompareRunsHeader = () => (
  <div className=' bg-[#1d1e20] box-border content-stretch flex items-center justify-between left-0 overflow-clip px-[24px] py-[16px] top-[48px] w-full'>
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
          <Link href={'/admin'}>
            <div className='flex-none rotate-[90deg] scale-y-[-100%]'>
              <ChevronUpIcon />
            </div>
          </Link>
        </div>
        <div className='content-stretch flex flex-col gap-[4px] h-[48px] items-start leading-[20px] relative shrink-0 text-[14px] w-[198px]'>
          <p
            className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold relative shrink-0 text-[#cecfd2] w-full"
            style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
          >
            Compare Runs
          </p>
          <p
            className="font-['Noto_Sans:Regular',sans-serif] font-normal relative shrink-0 text-[rgba(229,233,246,0.25)] w-full"
            style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
          >
            Agent: RockAgent_v1
          </p>
        </div>
      </div>
    </div>
  </div>
);
