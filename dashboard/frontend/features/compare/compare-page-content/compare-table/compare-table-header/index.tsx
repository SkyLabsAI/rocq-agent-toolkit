import { RunDetailsResponse } from "@/types/types";
import { Button } from "@/components/base";
import { SortIcon } from "@/icons/sort/sort";
import { ChevronUpIcon } from "@/icons/chevron-up";

interface TaskComparisonHeaderTopProps {
  runs: RunDetailsResponse[];
}

export const TaskComparisonHeaderTop: React.FC<TaskComparisonHeaderTopProps> = ({
  runs,
}) => (
  <>
  </>
 <div className='flex justify-between px-6 py-4 bg-elevation-surface items-center rounded-t-lg '>
          <p
            className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-5 relative shrink-0 text-[#cecfd2] text-[14px] text-nowrap whitespace-pre"
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
          <Button leftIcon={<SortIcon />} rightIcon={<ChevronUpIcon />} variant="default" rightDivider>
              Filter Fields
            </Button>
        </div>
    
);
