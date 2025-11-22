import { RunDetailsResponse } from "@/types/types";
import { RunTaskCell } from "../..";
import { ComparisonHeaderBar } from "../compare-header-bar";
import { TaskComparisonHeaderTop } from "./compare-table-header";
import React from "react";
import { TaskHeader } from "./compare-table-header/task-header";
import { TaskDetailsTable } from "./compare-table-header/task-details";

interface ComparisonTableProps {
  runs: RunDetailsResponse[];
  taskMap: Record<string, RunTaskCell[]>;
  allTaskIds: string[];
  selectedTaskId: string | null;
  onSelectTask: (taskId: string) => void;
  onOpenModal: (taskId: string) => void;
  showTasks: boolean;
  onToggleShowTasks: () => void;
}

export const ComparisonTable: React.FC<ComparisonTableProps> = ({
  runs,
  taskMap,
  allTaskIds,
  selectedTaskId,
  onSelectTask,
  onOpenModal,
  showTasks,
  onToggleShowTasks,
}) => {
  console.log('Rendering ComparisonTable with tasks:', taskMap);
  return (
    <>
      <ComparisonHeaderBar />
      <div className=' left-[40px] rounded-[4px] top-[336px] w-[1200px]'>
        <div className='content-stretch flex flex-col gap-px items-start overflow-clip relative rounded-[inherit] w-[1200px]'>
          <TaskComparisonHeaderTop runs={runs} />
          <>
            {allTaskIds != undefined &&
              allTaskIds.map(taskId => (
                <React.Fragment key={taskId}>
                  <TaskHeader
                    id={taskId}
                    details={taskMap[taskId]}
                  />
                  <TaskDetailsTable
                  id={taskId}
                  details={taskMap[taskId]}
                  />
                </React.Fragment>
              ))}
          </>
        </div>
        <div
          aria-hidden='true'
          className=' border border-[#2b2c2f] border-solid inset-0 pointer-events-none rounded-[4px]'
        />
      </div>
    </>
  );
};
