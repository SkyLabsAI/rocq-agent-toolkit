import { StatusBadge } from '@/components/base/statusBadge';
import { RunTaskCell } from '@/features/compare';
import { ChevronUpIcon } from '@/icons/chevron-up';
import { CompareDetailsButton } from './compare-details';
import { Button } from '@/components/base';
import { buildTailwindGridTemplate, getCommonGridStyle } from '..';
import style from 'react-syntax-highlighter/dist/esm/styles/hljs/a11y-dark';

export const TaskHeader = ({
  id,
  details,
  onOpenModal,
}: {
  id: string;
  details: RunTaskCell[];
  onOpenModal: (taskId: string) => void;
}) => (
  <div className={`grid py-2 bg-elevation-surface-raised px-6 `} style={getCommonGridStyle(details.length)}>
    <div className=' flex items-center gap-2  -left-3 relative w-[242px]'>
      <ChevronUpIcon className='rotate-180 size-6 flex justify-center items-center' />
      <p
        className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-[20px] relative shrink-0 text-[#cecfd2] text-[14px]"
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
      <Button className='float-right' variant='default' onClick={()=>onOpenModal(id)}>
        Compare Details
      </Button>
    </div>
  </div>
);
