import cn from "classnames";
import { useAgentDetails } from "@/hooks/useAgentDetails";
import AgentRunsView from "./AgentRunsView";
import { useEffect } from "react";

interface AgentDetailsProps {
  agent_name: string;
  adminView?: boolean;
  activeAgent?: boolean;
   setActiveAgent: (agent: string) => void;
}

const AgentDetails: React.FC<AgentDetailsProps> = ({ agent_name, adminView=false, activeAgent=false,setActiveAgent }) => {
  const {
    loading,
    taskDetails,
    runDetails,
    isOpen,
    selectedRuns,
    toggleDetails,
    compareSelected,
    toggleRunSelection,
    clearSelectedRuns,
    
  } = useAgentDetails(agent_name, setActiveAgent);

   useEffect(() => {
    if (!activeAgent) {
      clearSelectedRuns();
    }
  }, [activeAgent]);

  return (
    <>
      <tr
        className={cn(
          "hover:bg-white/5 cursor-pointer transition-colors duration-200",

        )}
        onClick={toggleDetails}
      >
        <td className="px-6 py-4 text-text font-medium">
          <div className="flex items-center gap-3">
            <div className="h-6 w-6 bg-background-information rounded-lg flex items-center justify-center">
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
          <td colSpan={7}>
            <div className="px-6">
              {loading ? (
                <div className="flex items-center justify-center py-8">
                  <div className="animate-spin rounded-full h-8 w-8 border-b-2 border-blue-400"></div>
                  <span className="ml-3 text-gray-400">
                    Loading task details...
                  </span>
                </div>
              ) : (adminView ? runDetails.length === 0 : taskDetails.length === 0) ? (
                <div className="text-center py-8 text-text">
                  No {adminView ? 'run' : 'task'} details available.
                </div>
              ) : (
                <div className="space-y-4">
                <AgentRunsView
                      runDetails={runDetails}
                      agentName={agent_name}
                      selectedRuns={selectedRuns}
                      toggleRunSelection={toggleRunSelection}
                      clearSelectedRuns={clearSelectedRuns}
                      compareSelected={compareSelected}
                    />
                </div>
              )}
            </div>
          </td>
        </tr>
      )}
    </>
  );
};

export default AgentDetails;
