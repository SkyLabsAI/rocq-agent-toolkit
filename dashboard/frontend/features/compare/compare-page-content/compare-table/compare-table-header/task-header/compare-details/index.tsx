export const CompareDetailsButton = () => (
  <div
    className='relative rounded-[4px] shrink-0'
    onClick={e => {
      e.stopPropagation();
    //   setComparisonModalTaskId(taskId);
    }}
  >
    <div className='box-border content-stretch flex gap-[6px] items-center overflow-clip pl-[12px] pr-[14px] py-[8px] relative rounded-[inherit]'>
      <p
        className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-[20px] relative shrink-0 text-[#cecfd2] text-[14px] text-nowrap whitespace-pre"
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Compare Details
      </p>
    </div>
    <div
      aria-hidden='true'
      className=' border border-[#525865] border-solid inset-0 pointer-events-none rounded-[4px] shadow-[0px_1px_4px_0px_rgba(0,0,0,0.08)]'
    />
  </div>
);
