import { Button } from '@/components/base';
import { StatusBadge } from '@/components/base/statusBadge';
import { type RunTaskCell } from '@/features/runs-compare';
import { ChevronUpIcon } from '@/icons/chevron-up';
import { cn } from '@/utils/cn';

import { getCommonGridStyle } from '..';

export const TaskHeader = ({
  id,
  name,
  details,
  onOpenModal,
  isExpanded,
  onClick,
}: {
  id: number;
  name: string;
  details: RunTaskCell[];
  onOpenModal: (taskId: number) => void;
  onClick: () => void;
  isExpanded: boolean;
}) => (
  <div
    className={`grid py-2 bg-elevation-surface-raised px-6 `}
    style={getCommonGridStyle(details.length)}
    onClick={onClick}
  >
    <div className=' flex items-center gap-2  -left-3 relative'>
      <ChevronUpIcon
        className={cn('size-6 min-w-6 h-w-6', { 'rotate-180': isExpanded })}
      />
      <p
        className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-5 relative shrink-0 text-text text-[14px] truncate max-w-full"
        style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
      >
        Task Name: {name}
      </p>
    </div>

    {details.length > 0 &&
      details.map((detail, index) => (
        <StatusBadge key={index} status={detail.task?.status || 'Failure'} />
      ))}

    <div>
      <Button
        className='float-right'
        variant='outline'
        onClick={() => onOpenModal(id)}
      >
        Compare Details
      </Button>
    </div>
  </div>
);
