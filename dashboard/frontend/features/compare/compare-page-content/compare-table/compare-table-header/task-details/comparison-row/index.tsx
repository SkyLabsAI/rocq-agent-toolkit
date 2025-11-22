export const ComparisonRow = ({
  label,
  value1,
  value2,
}: {
  label: string;
  value1: string;
  value2: string;
}) => (
  <div className='relative shrink-0 w-full'>
    <div className='flex flex-row items-center overflow-clip rounded-[inherit] size-full'>
      <div className='box-border content-stretch flex items-center justify-between px-[24px] py-[4px] relative w-full'>
        <div className='basis-0 grow min-h-px min-w-px relative shrink-0'>
          <div className='flex flex-row items-center size-full'>
            <div className='box-border content-stretch flex gap-[84px] items-center pl-[20px] pr-0 py-0 relative w-full'>
              <p
                className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-[20px] relative shrink-0 text-[#cecfd2] text-[14px] w-[230px]"
                style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
              >
                {label}
              </p>
              <div className='h-[20px] relative shrink-0 w-[242px]'>
                <p
                  className=" font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-[20px] left-0 text-[#cecfd2] text-[14px] text-nowrap top-0 whitespace-pre"
                  style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
                >
                  {value1}
                </p>
              </div>
              <div className='h-[20px] relative shrink-0 w-[273px]'>
                <p
                  className=" font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-[20px] left-0 text-[#cecfd2] text-[14px] text-nowrap top-0 whitespace-pre"
                  style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
                >
                  {value2}
                </p>
              </div>
            </div>
          </div>
        </div>
      </div>
    </div>
    <div
      aria-hidden='true'
      className=' border-[#2b2c2f] border-[0px_0px_1px] border-solid inset-0 pointer-events-none'
    />
  </div>
);

export const ComparisonRowLast = ({
  label,
  value1,
  value2,
}: {
  label: string;
  value1: string;
  value2: string;
}) => (
  <div className='relative rounded-bl-[4px] rounded-br-[4px] shrink-0 w-full'>
    <div className='flex flex-row items-center overflow-clip rounded-[inherit] size-full'>
      <div className='box-border content-stretch flex items-center justify-between px-[24px] py-[4px] relative w-full'>
        <div className='basis-0 grow min-h-px min-w-px relative shrink-0'>
          <div className='flex flex-row items-center size-full'>
            <div className='box-border content-stretch flex gap-[84px] items-center pl-[20px] pr-0 py-0 relative w-full'>
              <p
                className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-[20px] relative shrink-0 text-[#cecfd2] text-[14px] w-[230px]"
                style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
              >
                {label}
              </p>
              <div className='h-[20px] relative shrink-0 w-[242px]'>
                <p
                  className=" font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-[20px] left-0 text-[#cecfd2] text-[14px] text-nowrap top-0 whitespace-pre"
                  style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
                >
                  {value1}
                </p>
              </div>
              <div className='h-[20px] relative shrink-0 w-[273px]'>
                <p
                  className=" font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-[20px] left-0 text-[#cecfd2] text-[14px] text-nowrap top-0 whitespace-pre"
                  style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
                >
                  {value2}
                </p>
              </div>
            </div>
          </div>
        </div>
      </div>
    </div>
  </div>
);
