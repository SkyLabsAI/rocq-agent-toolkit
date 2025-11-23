import { Button } from "@/components/base";
import { RunStats } from "@/features/compare";

export const TaskRow: React.FC<{ stat: RunStats }> = ({ stat }) => (
  <div className=' bg-elevation-surface box-border gap-10 content-stretch flex items-center left-10 px-6 py-2.5  top-19 mt-[13px] rounded-lg'>

      <div className='content-stretch flex gap-10 items-center relative shrink-0 w-1/4'>
        <p
          className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-text text-[14px] text-nowrap whitespace-pre"
          style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
        >
          {stat.id}
        </p>
      </div>

        <div className='content-stretch flex flex-col gap-2.5 items-center justify-center relative shrink-0 w-1/12'>
          <p
            className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-text text-[14px] w-full"
            style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
          >
            {stat.tasks}
          </p>
        </div>
        <div className='content-stretch flex flex-col gap-[10px] items-center justify-center relative shrink-0 w-1/12'>
          <p
            className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-text text-[14px] w-full"
            style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
          >
            {stat.successRate.toFixed(2)}%
          </p>
        </div>
        <div className='content-stretch flex flex-col gap-[10px] items-center justify-center relative shrink-0 w-1/12'>
          <p
            className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-text text-[14px] w-full"
            style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
          >
            {stat.totalLlmCalls}
          </p>
        </div>
        <div className='content-stretch flex flex-col gap-[10px] items-center justify-center relative shrink-0 w-1/12'>
          <p
            className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-text text-[14px] w-full"
            style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
          >
            {stat.totalTokens}
          </p>
        </div>
        <div className='content-stretch flex flex-col gap-[10px] items-center justify-center relative shrink-0 w-1/12'>
          <p
            className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-text text-[14px] w-full"
            style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
          >
            {stat.avgExecutionTime.toFixed(2)}
          </p>
        </div>
 
<div className="flex-1">
 <Button variant="danger" className="float-end self-end">
      Remove
    </Button>
</div>

  </div>
);