import { getCommonGridStyle } from '../..';

export const ComparisonRow = ({
  label,
  values,
}: {
  label: string;
  values: string[];
}) => (
  <div className='grid px-6 py-1' style={getCommonGridStyle(3)}>
    <p
      className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-5 relative shrink-0 text-[#cecfd2] text-[14px] w-[230px]  ml-5"
      style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
    >
      {label}
    </p>

    {values !=undefined && values.map((value, index) => (
      <div className='h-5 relative shrink-0 ' key={index}>
        <p
          className=" font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-5 left-0 text-[#cecfd2] text-[14px] text-nowrap top-0 whitespace-pre"
          style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
        >
          {value}
        </p>
      </div>
    ))}

    <div className=''></div>
  </div>
);
