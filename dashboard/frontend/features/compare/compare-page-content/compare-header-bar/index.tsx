// Comparison Section Components
export const ComparisonHeaderBar = () => (
  <div className=' bg-[#1d1e20] box-border content-stretch flex items-center justify-between left-[40px] overflow-clip px-[24px] py-[16px] rounded-[4px] top-[336px] w-[1200px]'>
    <div className='basis-0 content-stretch flex grow items-center justify-between min-h-px min-w-px relative shrink-0'>
      <p
        className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-5 relative shrink-0 text-[#cecfd2] text-[14px] text-nowrap whitespace-pre"
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Taskwise Comparison
      </p>
      <p
        className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-5 relative shrink-0 text-[#cecfd2] text-[14px] text-nowrap whitespace-pre"
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Run_RocqAgent_001
      </p>
      <p
        className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-5 relative shrink-0 text-[#cecfd2] text-[14px] text-nowrap whitespace-pre"
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Run_RocqAgent_002
      </p>
      {/* <FilterFieldsButton /> */}
    </div>
  </div>
);