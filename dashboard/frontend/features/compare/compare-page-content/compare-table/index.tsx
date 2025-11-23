import { RunDetailsResponse } from "@/types/types";
import {  RunTaskCell } from "../..";
import { TaskComparisonHeaderTop } from "./compare-table-header";
import React from "react";
import { TaskHeader } from "./compare-table-header/task-header";
import { TaskDetailsTable } from "./compare-table-header/task-details";
import { TaskRowData } from "../utils";

interface ComparisonTableProps {
  runs: RunDetailsResponse[];
  taskMap: Record<string, RunTaskCell[]>;
  allTaskIds: string[];
  selectedTaskId: string | null;
  onSelectTask: (taskId: string) => void;
  onOpenModal: (taskId: string) => void;
  showTasks: boolean;
  taskRowData: TaskRowData[];
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
  taskRowData,
  onToggleShowTasks,
}) => {
  console.log('Rendering ComparisonTable with tasks:', taskMap);
  return (
    <>

      <div className='mt-10 border border-elevation-surface-overlay rounded-lg  bg-elevation-surface'>
        <div className='items-center '>
          <TaskComparisonHeaderTop runs={runs} />
          <>
            {allTaskIds != undefined &&
              allTaskIds.map(taskId => (
                <React.Fragment key={taskId}>
                  <TaskHeader
                    id={taskId}
                    details={taskMap[taskId]}
                    onOpenModal={onOpenModal}
                  />
                  <TaskDetailsTable
                  id={taskId}
                  details={taskMap[taskId]}
                  taskRowData={taskRowData.find(row => row.taskId === taskId)!}
                  />
                </React.Fragment>
              ))}
          </>
        </div>
       
      </div>
    </>
  );
};
