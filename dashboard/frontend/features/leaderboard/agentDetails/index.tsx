import TaskButton from "@/components/base/taskButton";
import TaskDetailsModal from "@/features/taskDetailsModal";
import cn from "classnames";
import { useAgentDetails } from "@/hooks/useAgentDetails";
import { PlayIcon } from "@/icons/play";
import AgentRunsView from "./AgentRunsView";
import AgentTasksView from "./AgentTasksView";

interface AgentDetailsProps {
  agent_name: string;
  adminView?: boolean;
}

const AgentDetails: React.FC<AgentDetailsProps> = ({ agent_name, adminView=false }) => {
  const {
    loading,
    taskDetails,
    runDetails,
    runTaskDetails,
    loadingRunDetails,
    isOpen,
    modalState,
    selectedRuns,
    expandedRuns,
    loadingLogs,
    toggleDetails,
    openCodeModal,
    closeModal,
    toggleRunExpansion,
    compareSelected,
    toggleRunSelection,
    clearSelectedRuns,
  } = useAgentDetails(agent_name);

  return (
    <>
      <tr
        className={cn(
          "hover:bg-white/5 cursor-pointer transition-colors duration-200",
          { "bg-white/5": isOpen }
        )}
        onClick={toggleDetails}
      >
        <td className="px-6 py-4 text-text font-medium">
          <div className="flex items-center gap-3">
            <div className="h-8 w-8 bg-background-information rounded-lg flex items-center justify-center">
              <span className="text-text-information font-semibold text-sm">
                {agent_name.charAt(0).toUpperCase()}
              </span>
            </div>
            <span className="truncate">{agent_name}</span>
          </div>
        </td>
      </tr>

      {isOpen && (
        <tr>
          <td colSpan={7} className="bg-white/5 border-t border-white/10">
            <div className="p-6 pt-4">
              {loading ? (
                <div className="flex items-center justify-center py-8">
                  <div className="animate-spin rounded-full h-8 w-8 border-b-2 border-blue-400"></div>
                  <span className="ml-3 text-gray-400">
                    Loading task details...
                  </span>
                </div>
              ) : (adminView ? runDetails.length === 0 : taskDetails.length === 0) ? (
                <div className="text-center py-8 text-gray-400">
                  No {adminView ? 'run' : 'task'} details available.
                </div>
              ) : (
                <div className="space-y-4">
                  
                
                  {adminView ? (
                    <AgentRunsView
                      runDetails={runDetails}
                      agentName={agent_name}
                      selectedRuns={selectedRuns}
                      loadingLogs={loadingLogs}
                      toggleRunSelection={toggleRunSelection}
                      clearSelectedRuns={clearSelectedRuns}
                      compareSelected={compareSelected}
                      openCodeModal={openCodeModal}
                    />
                  ) : (
                    <AgentTasksView
                      taskDetails={taskDetails}
                      loadingLogs={loadingLogs}
                      openCodeModal={openCodeModal}
                    />
                  )}
                </div>
              )}
            </div>
          </td>
        </tr>
      )}

      {/* Task Details Modal */}
      <TaskDetailsModal
        isOpen={modalState.isOpen}
        onClose={closeModal}
        details={modalState.logs}
        title={modalState.selectedTask ? `Observability Logs - ${modalState.selectedTask.task_id}` : 'Task Logs'}
        taskId={modalState.selectedTask?.task_id}
      />
    </>
  );
};

export default AgentDetails;
