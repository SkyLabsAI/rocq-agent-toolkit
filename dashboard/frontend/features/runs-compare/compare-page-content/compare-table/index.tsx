import React, { useState } from 'react';

import { type RunDetailsResponse } from '@/types/types';

import { type RunTaskCell } from '../..';
import { type TaskRowData } from '../utils';
import { TaskComparisonHeaderTop } from './compare-table-header';
import { TaskDetailsTable } from './compare-table-header/task-details';
import { TaskHeader } from './compare-table-header/task-header';

interface ComparisonTableProps {
  runs: RunDetailsResponse[];
  taskMap: Record<string, RunTaskCell[]>;
  allTaskIds: number[];
  selectedTaskId: number | null;
  onSelectTask: (taskId: number) => void;
  onOpenModal: (taskId: number) => void;
  showTasks: boolean;
  taskRowData: TaskRowData[];
  onToggleShowTasks: () => void;
}

export const ComparisonTable: React.FC<ComparisonTableProps> = ({
  runs,
  taskMap,
  allTaskIds,
  onOpenModal,
  taskRowData,
}) => {
  return (
    <>
      <div className='mt-10 border border-elevation-surface-overlay rounded-lg  bg-elevation-surface'>
        <div className='items-center '>
          <TaskComparisonHeaderTop runs={runs} />
          <>
            {allTaskIds != undefined &&
              allTaskIds.map(taskId => (
                <TaskSection
                  key={taskId}
                  id={taskId}
                  details={taskMap[taskId]}
                  onOpenModal={onOpenModal}
                  taskRowData={taskRowData.find(row => row.taskId === taskId)!}
                />
              ))}
          </>
        </div>
      </div>
    </>
  );
};

interface TaskSectionProps {
  id: number;
  details: RunTaskCell[];
  onOpenModal: (taskId: number) => void;
  taskRowData: TaskRowData;
}

const TaskSection: React.FC<TaskSectionProps> = ({
  id,
  details,
  onOpenModal,
  taskRowData,
}) => {
  const [open, setOpen] = useState(true);

  return (
    <>
      <TaskHeader
        id={id}
        details={details}
        onOpenModal={onOpenModal}
        onClick={() => setOpen(!open)}
        isExpanded={open}
      />
      {open && <TaskDetailsTable taskRowData={taskRowData} />}
    </>
  );
};
