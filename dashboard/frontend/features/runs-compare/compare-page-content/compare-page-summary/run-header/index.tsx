import { PlayIcon } from '@/icons/play';
import React from 'react';

interface RunHeaderProps {
  title: string;
  keys: string[];
}

export const RunsHeader: React.FC<RunHeaderProps> = ({ title, keys }) => (
  <div className='flex items-center left-[54px] top-[19px] w-full mt-[19px] text-text-disabled gap-10 px-6'>
    <div className='content-stretch flex w-1/4 col-start-1 gap-1 items-center relative shrink-0 text-text'>
      <PlayIcon />
      <p
        className="font-['Noto_Sans:Regular',sans-serif] font-normal leading-4 relative shrink-0 text-text text-[16px] text-nowrap whitespace-pre"
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        {title}
      </p>
    </div>

    {keys.map(key => (
      <p
        key={key}
        className='relative shrink-0 w-1/12'
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        {key}
      </p>
    ))}
  </div>
);
