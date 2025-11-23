import { StatusBadge } from "@/components/base/statusBadge";
import { RunTaskCell } from "@/features/compare";
import { ChevronUpIcon } from "@/icons/chevron-up";
import { CompareDetailsButton } from "./compare-details";

export const TaskHeader = ({
  id,
  details,
}: {
  id: string;
  details: RunTaskCell[];
}) => (
  <div className='bg-[#222326] h-[52px] relative rounded-bl-[4px] rounded-br-[4px] shrink-0 w-full'>
    <div className='flex flex-row items-center overflow-clip rounded-[inherit] size-full'>
      <div className='box-border content-stretch flex h-[52px] items-center justify-between px-[24px] py-[8px] relative w-full'>
        <div className='basis-0 grow min-h-px min-w-px relative shrink-0'>
          <div className='flex flex-row items-center size-full'>
            <div className='box-border content-stretch flex gap-[84px] items-center pl-[20px] pr-0 py-0 relative w-full'>
               <div className=' flex items-center justify-center left-[12px] size-[24px] top-[14px]'>
          <div className='flex-none rotate-[180deg] scale-y-[-100%]'>
            <ChevronUpIcon />
          </div>
        </div>
             
              <p
                className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-[20px] relative shrink-0 text-[#cecfd2] text-[14px] w-[230px]"
                style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
              >
                Task ID: {id}
              </p>
              {details.length > 0 &&
                details.map((detail, index) => <StatusBadge key={index} status={detail.task?.status || "Failure"} />)}

              <CompareDetailsButton />
            </div>
          </div>
        </div>

      </div>
    </div>
  </div>
);