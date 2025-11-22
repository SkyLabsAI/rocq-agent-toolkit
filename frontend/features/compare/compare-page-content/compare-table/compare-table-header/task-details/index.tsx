import { RunTaskCell } from "@/features/compare";
import { ComparisonRow, ComparisonRowLast } from "./comparison-row";

export const TaskDetailsTable = ({ id, details }: { id: string; details: RunTaskCell[] }) => {
  console.log('Rendering TaskDetailsTable for taskId:', id, 'with details:', details);
  return <div className='bg-[#1d1e20] box-border content-stretch flex flex-col gap-px items-start px-0 py-[8px] relative shrink-0 w-full'>
    <ComparisonRow label='Calls' value1='20' value2='20' />
    <ComparisonRow label='Total Tokens' value1='10' value2='20' />
    <ComparisonRow label='input Tokens' value1='30' value2='25' />
    <ComparisonRow label='Output Tokens' value1='5' value2='3' />
    <ComparisonRow label='Exec Time (s)' value1='12' value2='8' />
    <ComparisonRow label='CPU Time (s)' value1='4' value2='2' />
    <ComparisonRowLast label='GPU Time (s)' value1='4' value2='2' />
  </div>
}


