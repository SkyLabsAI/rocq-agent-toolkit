import { RunStats } from "@/features/compare";

export const TaskRow: React.FC<{ stat: RunStats }> = ({ stat }) => (
  <div className=' bg-[#1d1e20] box-border content-stretch flex items-center justify-between left-[40px] px-[24px] py-[10px] rounded-[4px] top-[56px] '>
    <div className='content-stretch flex gap-[207px] items-center relative shrink-0'>
      <div className='content-stretch flex gap-[8px] items-center relative shrink-0'>
        <p
          className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-[#cecfd2] text-[14px] text-nowrap whitespace-pre"
          style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
        >
          {stat.name}
        </p>
      </div>
      <div className='content-stretch flex items-center relative shrink-0'>
        <div className='content-stretch flex flex-col gap-[10px] items-center justify-center relative shrink-0 w-[100px]'>
          <p
            className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-[#cecfd2] text-[14px] w-full"
            style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
          >
            {stat.tasks}
          </p>
        </div>
        <div className='content-stretch flex flex-col gap-[10px] items-center justify-center relative shrink-0 w-[137px]'>
          <p
            className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-[#cecfd2] text-[14px] w-full"
            style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
          >
            {stat.successRate}%
          </p>
        </div>
        <div className='content-stretch flex flex-col gap-[10px] items-center justify-center relative shrink-0 w-[132px]'>
          <p
            className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-[#cecfd2] text-[14px] w-full"
            style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
          >
            {stat.totalLlmCalls}
          </p>
        </div>
        <div className='content-stretch flex flex-col gap-[10px] items-center justify-center relative shrink-0 w-[151px]'>
          <p
            className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-[#cecfd2] text-[14px] w-full"
            style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
          >
            {stat.totalTokens}
          </p>
        </div>
        <div className='content-stretch flex flex-col gap-[10px] items-center justify-center relative shrink-0 w-[158px]'>
          <p
            className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-[#cecfd2] text-[14px] w-full"
            style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
          >
            {stat.avgExecutionTime}
          </p>
        </div>
      </div>
    </div>
    <div className='bg-[#42221f] relative rounded-[4px] shrink-0'>
      <div className='box-border content-stretch flex gap-[6px] items-center overflow-clip pl-[12px] pr-[14px] py-[8px] relative rounded-[inherit]'>
        <p
          className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-[#ff383c] text-[14px] text-nowrap whitespace-pre"
          style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
        >
          Remove
        </p>
      </div>
      <div
        aria-hidden='true'
        className=' border border-[#5d1f1a] border-solid inset-0 pointer-events-none rounded-[4px] shadow-[0px_1px_4px_0px_rgba(0,0,0,0.08)]'
      />
    </div>
  </div>
);