import { StatusBadge } from '@/components/base/statusBadge';
import { RunTaskCell } from '@/features/compare';
import { ChevronUpIcon } from '@/icons/chevron-up';
import { CompareDetailsButton } from './compare-details';
import { Button } from '@/components/base';
import {  getCommonGridStyle } from '..';
import style from 'react-syntax-highlighter/dist/esm/styles/hljs/a11y-dark';
import { cn } from '@/utils/cn';

export const TaskHeader = ({
  id,
  details,
  onOpenModal,
  isExpanded,
  onClick,
}: {
  id: string;
  details: RunTaskCell[];
  onOpenModal: (taskId: string) => void;
  onClick: () => void;
  isExpanded: boolean;
}) => (
  <div className={`grid py-2 bg-elevation-surface-raised px-6 `} style={getCommonGridStyle(details.length)} onClick={onClick} >
    <div className=' flex items-center gap-2  -left-3 relative w-[242px]'>
      <ChevronUpIcon className={cn('size-6',{"rotate-180": isExpanded})} />
      <p
        className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-5 relative shrink-0 text-[#cecfd2] text-[14px]"
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Task ID: {id}
      </p>
    </div>

    {details.length > 0 &&
      details.map((detail, index) => (
        <StatusBadge key={index} status={detail.task?.status || 'Failure'} />
      ))}

    <div >
      <Button className='float-right' variant='outline' onClick={()=>onOpenModal(id)}>
        Compare Details
      </Button>
    </div>
  </div>
);
