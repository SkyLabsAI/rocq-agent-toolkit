import { RunDetailsResponse } from '@/types/types';
import { Button } from '@/components/base';
import { SortIcon } from '@/icons/sort/sort';
import { ChevronUpIcon } from '@/icons/chevron-up';

interface TaskComparisonHeaderTopProps {
  runs: RunDetailsResponse[];
}


export function buildTailwindGridTemplate(length: number): string {
  const first = "230px";
  const last = "165px";
  const middle = Array.from({ length }, () => "minmax(0,1fr)");
  const cols = [first, ...middle, last];

  // CORRECT: No backticks around the bracket syntax
  // Output: [grid-template-columns:230px_minmax(0,1fr)_165px]
  return `[grid-template-columns:${cols.join("_")}]`;
}


export const getCommonGridStyle = (runCount: number) => {
  return {
    display: 'grid',
    // 230px Start | Dynamic Middle | 165px End
    gridTemplateColumns: `230px repeat(${runCount}, minmax(0, 1fr)) 165px`,
    alignItems: 'center',
    columnGap: '1rem' // This replaces 'gap-4' to be safe
  };
};


export const TaskComparisonHeaderTop: React.FC<
  TaskComparisonHeaderTopProps
> = ({ runs }) => (
  <div className={`grid px-6 py-4`} style={getCommonGridStyle(runs.length)}>
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
          className="font-['Noto_Sans:SemiBold',sans-serif] font-semibold leading-5relative shrink-0 text-[#cecfd2] text-[14px] text-nowrap whitespace-pre truncate"
          style={{ fontVariationSettings: "'CTGR' 0, 'wdth' 100" }}
        >
          { run.run_id}
        </p>
      ))}
    <div>
      <Button
        leftIcon={<SortIcon />}
        rightIcon={<ChevronUpIcon />}
        variant='default'
        rightDivider
        className='ml-auto float-end'
      >
        Filter Fields
      </Button>
    </div>
  </div>
);
