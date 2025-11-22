import { PlayIcon } from "@/icons/play";

export const RunsHeader = () => (
  <div className='content-stretch flex gap-[260px] items-center left-[54px] top-[19px] w-[1030px]'>
    <div className='content-stretch flex gap-[4px] items-center relative shrink-0'>
      <PlayIcon />
      <p
        className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-[#cecfd2] text-[16px] text-nowrap whitespace-pre"
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Runs
      </p>
    </div>
    <div className="box-border content-stretch flex font-['Noto_Sans:Regular',sans-serif] font-normal gap-[61px] items-center leading-[20px] px-[19px] py-0 relative shrink-0 text-[16px] text-[rgba(229,233,246,0.25)] text-nowrap whitespace-pre">
      <p
        className='relative shrink-0'
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Tasks
      </p>
      <p
        className='relative shrink-0'
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Success %
      </p>
      <p
        className='relative shrink-0'
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        LLM Calls
      </p>
      <p
        className='relative shrink-0'
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Total Token
      </p>
      <p
        className='relative shrink-0'
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Avg Exec Time (s)
      </p>
    </div>
  </div>
);

