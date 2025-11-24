import { PlayIcon } from '@/icons/play';

export const RunsHeader = () => (
  <div className='flex items-center left-[54px] top-[19px] w-full mt-[19px] text-text-disabled gap-10 px-6'>


    <div className='content-stretch flex w-1/4 col-start-1 gap-[4px] items-center relative shrink-0 text-text'>
      <PlayIcon />
      <p
        className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-4 relative shrink-0 text-text text-[16px] text-nowrap whitespace-pre"
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Runs
      </p>
    </div>

      <p
        className='relative shrink-0 w-1/12'
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Tasks
      </p>
      <p
        className='relative shrink-0 w-1/12'
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Success %
      </p>
      <p
        className='relative shrink-0 w-1/12'
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        LLM Calls
      </p>
      <p
        className='relative shrink-0 w-1/12'
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Total Token
      </p>
      <p
        className='relative shrink-0 w-1/12'
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Avg Exec Time (s)
      </p>


    
  </div>
);
