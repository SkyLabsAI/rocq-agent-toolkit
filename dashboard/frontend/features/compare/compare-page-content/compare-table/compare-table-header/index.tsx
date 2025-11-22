import { RunDetailsResponse } from "@/types/types";
import { FilterFieldsButton } from "./filter-fields";

interface TaskComparisonHeaderTopProps {
  runs: RunDetailsResponse[];
}

export const TaskComparisonHeaderTop: React.FC<TaskComparisonHeaderTopProps> = ({
  runs,
}) => (
  <div className='bg-[#1d1e20] h-[68px] relative rounded-tl-[4px] rounded-tr-[4px] shrink-0 w-full'>
    <div className='flex flex-row items-center overflow-clip rounded-[inherit] size-full'>
      <div className='box-border content-stretch flex h-[68px] items-center justify-between px-[24px] py-[16px] relative w-full'>
        <div className='basis-0 content-stretch flex grow items-center justify-between min-h-px min-w-px relative shrink-0'>
          <p
            className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-[20px] relative shrink-0 text-[#cecfd2] text-[14px] text-nowrap whitespace-pre"
            style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
          >
            Taskwise Comparison
          </p>
          {runs &&
            runs.map(run => (
              <p
                key={run.run_id}
                className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-[20px] relative shrink-0 text-[#cecfd2] text-[14px] text-nowrap whitespace-pre"
                style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
              >
                {run.agent_name || run.run_id}
              </p>
            ))}
          <FilterFieldsButton />
        </div>
      </div>
    </div>
  </div>
);
