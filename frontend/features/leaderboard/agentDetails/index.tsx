import TaskButton from "@/components/base/taskButton";
import TaskDetailsModal from "@/features/taskDetailsModal";
import {  TaskOutput, AgentRun } from "@/types/types";
import { useState } from "react";
import { useRouter } from "next/navigation";
import cn from "classnames";
import { getDetails, getRunDetails, getObservabilityLogs } from "@/services/dataservice";

interface AgentDetailsProps {
  agent_name: string;
  adminView?: boolean;
}

const AgentDetails: React.FC<AgentDetailsProps> = ({ agent_name, adminView=false }) => {
  const [loading, setLoading] = useState<boolean>(false);
  const [taskDetails, setTaskDetails] = useState<TaskOutput[]>([]);
  const [runDetails, setRunDetails] = useState<AgentRun[]>([]);
  const [runTaskDetails, setRunTaskDetails] = useState<Map<string, TaskOutput[]>>(new Map());
  const [loadingRunDetails, setLoadingRunDetails] = useState<Set<string>>(new Set());
  const [isOpen, setIsOpen] = useState<boolean>(false);
  const [modalState, setModalState] = useState<{
    isOpen: boolean;
    selectedTask: TaskOutput | null;
    logs: Record<string, unknown> | null;
  }>({
    isOpen: false,
    selectedTask: null,
    logs: null
  });
  const [selectedRuns, setSelectedRuns] = useState<string[]>([]);
  const [expandedRuns, setExpandedRuns] = useState<Set<string>>(new Set());
  const [loadingLogs, setLoadingLogs] = useState<string | null>(null);
  const router = useRouter();

  const openDetails = async () => {
    setLoading(true);
    try {
      // For now, we'll use the agent data directly since we have the full structure
      // In a real app, this might be an API call
     await getDetails(agent_name).then(data => {
      setRunDetails(data);
     });
     setTaskDetails([]);
    

    } catch (error) {
      console.error(error);
    } finally {
      setLoading(false);
    }
  };

  const toggleDetails = () => {
    return isOpen
      ? setIsOpen(false)
      : openDetails().then(() => setIsOpen(true));
  };

  const openCodeModal = async (task: TaskOutput) => {
    const taskKey = `${task.run_id}-${task.task_id}`;
    setLoadingLogs(taskKey);
    
    try {
      // Fetch observability logs for this specific task
      const logs = await getObservabilityLogs(task.run_id, task.task_id);
      
      setModalState({
        isOpen: true,
        selectedTask: task,
        logs: logs
      });
    } catch (error) {
      console.error('Error fetching observability logs:', error);
      // Still open modal but with empty logs
      setModalState({
        isOpen: true,
        selectedTask: task,
        logs: { error: 'Failed to load logs' }
      });
    } finally {
      setLoadingLogs(null);
    }
  };
  const toggleRunSelection = (runId: string) => {
    setSelectedRuns(prev => prev.includes(runId) ? prev.filter(id => id !== runId) : [...prev, runId]);
  };

  const toggleRunExpansion = async (runId: string) => {
    setExpandedRuns(prev => {
      const newSet = new Set(prev);
      if (newSet.has(runId)) {
        newSet.delete(runId);
      } else {
        newSet.add(runId);
        // Fetch run details when expanding
        fetchRunDetails(runId);
      }
      return newSet;
    });
  };

  const fetchRunDetails = async (runId: string) => {
    // Check if we already have the data
    if (runTaskDetails.has(runId)) {
      return;
    }

    setLoadingRunDetails(prev => new Set([...prev, runId]));
    
    try {
      const response = await getRunDetails([runId]);
      if (response && response.length > 0) {
        const runDetail = response[0];
        setRunTaskDetails(prev => new Map([...prev, [runId, runDetail.tasks]]));
      }
    } catch (error) {
      console.error('Error fetching run details:', error);
      // Optionally show an error toast or message
    } finally {
      setLoadingRunDetails(prev => {
        const newSet = new Set(prev);
        newSet.delete(runId);
        return newSet;
      });
    }
  };

  const compareSelected = () => {
    if (selectedRuns.length < 1) return;
    const query = new URLSearchParams({
      agent: agent_name,
      runs: selectedRuns.join(',')
    }).toString();
    router.push(`/admin/compare?${query}`);
  };

  const closeModal = () => {
    setModalState(prev => ({ ...prev, isOpen: false, selectedTask: null, logs: null }));
  };

  return (
    <>
      <tr
        className={cn(
          "hover:bg-white/5 cursor-pointer transition-colors duration-200",
          { "bg-white/5": isOpen }
        )}
        onClick={toggleDetails}
      >
        <td className="px-6 py-4 text-white font-medium">
          <div className="flex items-center gap-3">
            <div className="h-8 w-8 bg-blue-500/20 rounded-lg flex items-center justify-center">
              <span className="text-blue-400 font-semibold text-sm">
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
            <div className="p-6">
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
                  <h3 className="text-lg font-semibold text-white mb-4">
                    {adminView ? 'Run Details' : 'Task Details'}
                  </h3>
                  {adminView ? (
                    // Admin View: Show runs with their tasks
                    <div className="space-y-6">
                      {/* Admin view: Runs list with selectable compare actions */}
                      {runDetails.map((run) => (
                        <div key={run.run_id} className="border border-white/10 rounded-lg overflow-hidden">
                          <div 
                            className="bg-white/5 px-4 py-3 border-b border-white/10 cursor-pointer hover:bg-white/10 transition-colors"
                            onClick={() => toggleRunExpansion(run.run_id)}
                          >
                            <div className="flex items-center justify-between gap-4">
                              <div className="min-w-0 flex items-center gap-3">
                                <svg 
                                  className={cn(
                                    "h-4 w-4 text-gray-400 transition-transform",
                                    expandedRuns.has(run.run_id) ? "rotate-90" : ""
                                  )} 
                                  fill="none" 
                                  viewBox="0 0 24 24" 
                                  stroke="currentColor"
                                >
                                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 5l7 7-7 7" />
                                </svg>
                                <div className="flex-1 min-w-0">
                                  <div className="flex items-center gap-2 mb-1">
                                    <h4 className="text-lg font-medium text-white truncate" title={run.run_id}>{run.run_id}</h4>
                                    {runDetails.indexOf(run) === 0 && runDetails.length > 1 && (
                                      <span className="px-2 py-0.5 text-xs font-semibold rounded-full bg-blue-500/20 text-blue-300 border border-blue-500/30">
                                        Latest
                                      </span>
                                    )}
                                  </div>
                                  <div className="grid grid-cols-2 md:grid-cols-4 gap-4 text-xs">
                                    <div>
                                      <span className="text-gray-500">Total Tasks</span>
                                      <p className="font-medium text-white">{run.total_tasks}</p>
                                    </div>
                                    <div>
                                      <span className="text-gray-500">Success Rate</span>
                                      <p className="font-medium">
                                        <span className="text-green-400">{run.success_count}</span>
                                        <span className="text-gray-400">/</span>
                                        <span className="text-red-400">{run.failure_count}</span>
                                        <span className="text-gray-400 ml-1">({((run.success_count / run.total_tasks) * 100).toFixed(1)}%)</span>
                                      </p>
                                    </div>
                                    <div>
                                      <span className="text-gray-500">Agent</span>
                                      <p className="font-medium text-blue-400">{run.agent_name}</p>
                                    </div>
                                    <div>
                                      <span className="text-gray-500">Timestamp</span>
                                      <p className="font-mono text-gray-300" title={run.timestamp_utc}>
                                        {new Date(run.timestamp_utc).toLocaleString()}
                                      </p>
                                    </div>
                                  </div>
                                </div>
                              </div>
                              <div className="flex items-center gap-2">
                                <button
                                  type="button"
                                  onClick={(e) => { e.stopPropagation(); toggleRunSelection(run.run_id); }}
                                  className={cn(
                                    "px-3 py-1 rounded-md text-sm font-medium border transition-colors",
                                    selectedRuns.includes(run.run_id)
                                      ? "bg-green-500/20 border-green-500/40 text-green-300 hover:bg-green-500/30"
                                      : "bg-blue-500/10 border-blue-500/30 text-blue-300 hover:bg-blue-500/20"
                                  )}
                                >
                                  {selectedRuns.includes(run.run_id) ? 'Selected' : 'Add to Compare'}
                                </button>
                              </div>
                            </div>
                          </div>
                          {expandedRuns.has(run.run_id) && (
                            <div className="p-4 space-y-3">
                              {loadingRunDetails.has(run.run_id) ? (
                                <div className="flex items-center justify-center py-8">
                                  <div className="animate-spin rounded-full h-6 w-6 border-b-2 border-blue-400"></div>
                                  <span className="ml-3 text-gray-400">Loading tasks...</span>
                                </div>
                              ) : runTaskDetails.has(run.run_id) ? (
                                runTaskDetails.get(run.run_id)!.map((task) => (
                                  <div
                                    key={task.task_id}
                                    className="bg-white/10 border border-white/20 rounded-lg p-4 hover:bg-white/15 transition-colors shadow-lg"
                                  >
                                    <div className="space-y-4">
                                      {/* Basic Task Information */}
                                      <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
                                        <div>
                                          <label className="text-xs font-medium text-gray-400 uppercase tracking-wider">
                                            Task ID
                                          </label>
                                          <p className="text-white font-mono text-sm truncate" title={task.task_id}>
                                            {task.task_id}
                                          </p>
                                        </div>
                                        <div>
                                          <label className="text-xs font-medium text-gray-400 uppercase tracking-wider">
                                            Status
                                          </label>
                                          <div className="mt-1">
                                            <TaskButton status={task.status} />
                                          </div>
                                        </div>
                                        {task.trace_id && (
                                          <div>
                                            <label className="text-xs font-medium text-gray-400 uppercase tracking-wider">
                                              Trace ID
                                            </label>
                                            <p className="text-yellow-300 font-mono text-sm truncate" title={task.trace_id}>
                                              {task.trace_id}
                                            </p>
                                          </div>
                                        )}
                                        <div>
                                          <label className="text-xs font-medium text-gray-400 uppercase tracking-wider">
                                            Timestamp
                                          </label>
                                          <p className="text-gray-300 font-mono text-sm">
                                            {new Date(task.timestamp_utc).toLocaleString()}
                                          </p>
                                        </div>
                                      </div>

                                      {/* Task Kind and Agent Info */}
                                      <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
                                        <div>
                                          <label className="text-xs font-medium text-gray-400 uppercase tracking-wider">
                                            Task Kind
                                          </label>
                                          <p className="text-cyan-300 text-sm">
                                            {typeof task.task_kind === "object"
                                              ? task.task_kind.kind +
                                                ("value" in task.task_kind
                                                  ? ` (${task.task_kind.value})`
                                                  : "")
                                              : String(task.task_kind)}
                                          </p>
                                        </div>
                                        <div>
                                          <label className="text-xs font-medium text-gray-400 uppercase tracking-wider">
                                            Agent Name
                                          </label>
                                          <p className="text-blue-300 text-sm font-medium">
                                            {task.agent_name}
                                          </p>
                                        </div>
                                      </div>

                                      {/* Metrics Section */}
                                      <div>
                                        <h5 className="text-sm font-medium text-gray-300 mb-3 border-b border-gray-600 pb-1">
                                          Performance Metrics
                                        </h5>
                                        <div className="grid grid-cols-2 sm:grid-cols-3 lg:grid-cols-4 xl:grid-cols-5 gap-4">
                                          <div>
                                            <label className="text-xs font-medium text-blue-400 uppercase tracking-wider">
                                              LLM Calls
                                            </label>
                                            <p className="text-blue-300 font-bold text-lg">
                                              {task.metrics?.llm_invocation_count ?? "-"}
                                            </p>
                                          </div>
                                          <div>
                                            <label className="text-xs font-medium text-purple-400 uppercase tracking-wider">
                                              Total Tokens
                                            </label>
                                            <p className="text-purple-300 font-bold text-lg">
                                              {task.metrics?.token_counts?.total_tokens?.toLocaleString() ?? "-"}
                                            </p>
                                          </div>
                                          <div>
                                            <label className="text-xs font-medium text-green-400 uppercase tracking-wider">
                                              Input Tokens
                                            </label>
                                            <p className="text-green-300 font-bold text-sm">
                                              {task.metrics?.token_counts?.input_tokens?.toLocaleString() ?? "-"}
                                            </p>
                                          </div>
                                          <div>
                                            <label className="text-xs font-medium text-orange-400 uppercase tracking-wider">
                                              Output Tokens
                                            </label>
                                            <p className="text-orange-300 font-bold text-sm">
                                              {task.metrics?.token_counts?.output_tokens?.toLocaleString() ?? "-"}
                                            </p>
                                          </div>
                                          <div>
                                            <label className="text-xs font-medium text-red-400 uppercase tracking-wider">
                                              Execution Time
                                            </label>
                                            <p className="text-red-300 font-bold text-lg">
                                              {task.metrics?.resource_usage?.execution_time_sec?.toFixed(2) ?? "-"}s
                                            </p>
                                          </div>
                                          {task.metrics?.resource_usage?.cpu_time_sec !== undefined && (
                                            <div>
                                              <label className="text-xs font-medium text-yellow-400 uppercase tracking-wider">
                                                CPU Time
                                              </label>
                                              <p className="text-yellow-300 font-bold text-sm">
                                                {task.metrics.resource_usage.cpu_time_sec.toFixed(2)}s
                                              </p>
                                            </div>
                                          )}
                                          {task.metrics?.resource_usage?.gpu_time_sec !== undefined && (
                                            <div>
                                              <label className="text-xs font-medium text-pink-400 uppercase tracking-wider">
                                                GPU Time
                                              </label>
                                              <p className="text-pink-300 font-bold text-sm">
                                                {task.metrics.resource_usage.gpu_time_sec.toFixed(2)}s
                                              </p>
                                            </div>
                                          )}
                                        </div>
                                        
                                        {/* Custom Metrics */}
                                        {task.metrics?.custom_metrics && Object.keys(task.metrics.custom_metrics).length > 0 && (
                                          <div className="mt-3 pt-3 border-t border-gray-600">
                                            <h6 className="text-xs font-medium text-gray-400 uppercase tracking-wider mb-2">
                                              Custom Metrics
                                            </h6>
                                            <div className="grid grid-cols-2 md:grid-cols-3 gap-2">
                                              {Object.entries(task.metrics.custom_metrics).map(([key, value]) => (
                                                <div key={key}>
                                                  <label className="text-xs text-gray-500 capitalize">{key.replace(/_/g, ' ')}</label>
                                                  <p className="text-teal-300 font-medium text-sm">
                                                    {typeof value === 'number' ? value.toLocaleString() : String(value)}
                                                  </p>
                                                </div>
                                              ))}
                                            </div>
                                          </div>
                                        )}
                                      </div>

                                      {/* Task Results Section */}
                                      {task.results && (
                                        <div className="mt-4 pt-3 border-t border-gray-600">
                                          <h5 className="text-sm font-medium text-gray-300 mb-3">
                                            Task Results
                                          </h5>
                                          <div className="bg-black/30 border border-white/10 rounded-md p-3 font-mono text-xs whitespace-pre-wrap max-h-48 overflow-auto">
                                            {typeof task.results === 'string' ? 
                                              task.results : 
                                              JSON.stringify(task.results, null, 2)
                                            }
                                          </div>
                                        </div>
                                      )}
                                    </div>
                                    {task.failure_reason && (
                                      <div className="mt-3 pt-3 border-t border-red-500/20 bg-red-500/5 rounded p-2">
                                        <label className="text-xs font-medium text-red-300 uppercase tracking-wider">
                                          Failure Reason
                                        </label>
                                        <p className="text-red-200 text-sm font-medium">
                                          {Array.isArray(task.failure_reason) 
                                            ? task.failure_reason.join(', ') 
                                            : String(task.failure_reason)}
                                        </p>
                                      </div>
                                    )}
                                    <div className="mt-4 pt-3 border-t border-white/10">
                                      <button
                                        type="button"
                                        disabled={loadingLogs === `${task.run_id}-${task.task_id}`}
                                        onClick={(e) => {
                                          e.stopPropagation();
                                          openCodeModal(task);
                                        }}
                                        className={cn(
                                          "cursor-pointer inline-flex items-center px-4 py-2 border rounded-lg text-sm font-medium transition-colors duration-200",
                                          loadingLogs === `${task.run_id}-${task.task_id}`
                                            ? "bg-gray-500/10 border-gray-500/30 text-gray-500 cursor-not-allowed"
                                            : "bg-blue-500/10 hover:bg-blue-500/20 border-blue-500/30 text-blue-400"
                                        )}
                                      >
                                        {loadingLogs === `${task.run_id}-${task.task_id}` ? (
                                          <div className="animate-spin rounded-full h-4 w-4 mr-2 border-b-2 border-gray-500"></div>
                                        ) : (
                                          <svg className="h-4 w-4 mr-2" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                                            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M10 20l4-16m4 4l4 4-4 4M6 16l-4-4 4-4" />
                                          </svg>
                                        )}
                                        {loadingLogs === `${task.run_id}-${task.task_id}` ? 'Loading...' : 'View Logs'}
                                      </button>
                                    </div>
                                  </div>
                                ))
                              ) : (
                                <div className="text-center py-4 text-gray-400">
                                  Click to load task details
                                </div>
                              )}
                            </div>
                          )}
                        </div>
                      ))}
                      {runDetails.length > 0 && (
                        <div className="mt-6 pt-4 border-t border-white/10 flex items-center justify-between flex-wrap gap-4">
                          <div className="text-sm text-gray-400">
                            {selectedRuns.length === 0 ? 'Select runs to compare.' : `${selectedRuns.length} run${selectedRuns.length>1?'s':''} selected.`}
                          </div>
                          <div className="flex items-center gap-3">
                            {selectedRuns.length > 0 && (
                              <button
                                type="button"
                                onClick={(e) => { e.stopPropagation(); setSelectedRuns([]); }}
                                className="px-3 py-2 text-sm rounded-md bg-red-500/10 hover:bg-red-500/20 border border-red-500/30 text-red-300"
                              >
                                Clear Selection
                              </button>
                            )}
                            <button
                              type="button"
                              disabled={selectedRuns.length < 2}
                              onClick={(e) => { e.stopPropagation(); compareSelected(); }}
                              className={cn(
                                "px-4 py-2 text-sm rounded-md font-medium border transition-colors",
                                selectedRuns.length < 2
                                  ? "bg-gray-700 text-gray-400 border-gray-600 cursor-not-allowed"
                                  : "bg-purple-500/20 border-purple-500/40 text-purple-300 hover:bg-purple-500/30"
                              )}
                            >
                              {selectedRuns.length < 2 ? 'Select ≥ 2 runs' : 'Compare Selected'}
                            </button>
                          </div>
                        </div>
                      )}
                    </div>
                  ) : (
                    // Public View: Show tasks from latest run only
                    <div className="grid gap-3">
                      {taskDetails.map((task) => (
                      <div
                        key={task.run_id}
                        className="bg-white/10 border border-white/20 rounded-lg p-4 hover:bg-white/15 transition-colors shadow-lg"
                      >
                        <div className="space-y-4">
                          {/* Basic Task Information */}
                          <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
                            <div>
                              <label className="text-xs font-medium text-gray-400 uppercase tracking-wider">
                                Task ID
                              </label>
                              <p className="text-white font-mono text-sm truncate" title={task.task_id}>
                                {task.task_id}
                              </p>
                            </div>
                            <div>
                              <label className="text-xs font-medium text-gray-400 uppercase tracking-wider">
                                Status
                              </label>
                              <div className="mt-1">
                                <TaskButton status={task.status} />
                              </div>
                            </div>
                            <div>
                              <label className="text-xs font-medium text-gray-400 uppercase tracking-wider">
                                Run ID
                              </label>
                              <p className="text-gray-300 font-mono text-sm truncate" title={task.run_id}>
                                {task.run_id}
                              </p>
                            </div>
                            <div>
                              <label className="text-xs font-medium text-gray-400 uppercase tracking-wider">
                                Timestamp
                              </label>
                              <p className="text-gray-300 font-mono text-sm">
                                {new Date(task.timestamp_utc).toLocaleString()}
                              </p>
                            </div>
                            <div>
                              <label className="text-xs font-medium text-gray-400 uppercase tracking-wider">
                                Task Kind
                              </label>
                              <p className="text-cyan-300 text-sm">
                                {typeof task.task_kind === "object"
                                  ? task.task_kind.kind +
                                    ("value" in task.task_kind
                                      ? ` (${task.task_kind.value})`
                                      : "")
                                  : String(task.task_kind)}
                              </p>
                            </div>
                            {task.trace_id && (
                              <div>
                                <label className="text-xs font-medium text-gray-400 uppercase tracking-wider">
                                  Trace ID
                                </label>
                                <p className="text-yellow-300 font-mono text-sm truncate" title={task.trace_id}>
                                  {task.trace_id}
                                </p>
                              </div>
                            )}
                          </div>

                          {/* Performance Metrics */}
                          <div>
                            <h5 className="text-sm font-medium text-gray-300 mb-3 border-b border-gray-600 pb-1">
                              Performance Metrics
                            </h5>
                            <div className="grid grid-cols-2 sm:grid-cols-3 lg:grid-cols-4 xl:grid-cols-5 gap-4">
                              <div>
                                <label className="text-xs font-medium text-blue-400 uppercase tracking-wider">
                                  LLM Calls
                                </label>
                                <p className="text-blue-400 font-bold text-lg">
                                  {task.metrics?.llm_invocation_count ?? "-"}
                                </p>
                              </div>
                              <div>
                                <label className="text-xs font-medium text-purple-400 uppercase tracking-wider">
                                  Total Tokens
                                </label>
                                <p className="text-purple-400 font-bold text-lg">
                                  {task.metrics?.token_counts?.total_tokens?.toLocaleString() ?? "-"}
                                </p>
                              </div>
                              <div>
                                <label className="text-xs font-medium text-green-400 uppercase tracking-wider">
                                  Input Tokens
                                </label>
                                <p className="text-green-400 font-semibold">
                                  {task.metrics?.token_counts?.input_tokens?.toLocaleString() ?? "-"}
                                </p>
                              </div>
                              <div>
                                <label className="text-xs font-medium text-orange-400 uppercase tracking-wider">
                                  Output Tokens
                                </label>
                                <p className="text-orange-400 font-semibold">
                                  {task.metrics?.token_counts?.output_tokens?.toLocaleString() ?? "-"}
                                </p>
                              </div>
                              <div>
                                <label className="text-xs font-medium text-red-400 uppercase tracking-wider">
                                  Execution Time
                                </label>
                                <p className="text-red-400 font-bold text-lg">
                                  {task.metrics?.resource_usage?.execution_time_sec?.toFixed(2) ?? "-"}s
                                </p>
                              </div>
                              {task.metrics?.resource_usage?.cpu_time_sec !== undefined && (
                                <div>
                                  <label className="text-xs font-medium text-yellow-400 uppercase tracking-wider">
                                    CPU Time
                                  </label>
                                  <p className="text-yellow-400 font-semibold">
                                    {task.metrics.resource_usage.cpu_time_sec.toFixed(2)}s
                                  </p>
                                </div>
                              )}
                              {task.metrics?.resource_usage?.gpu_time_sec !== undefined && (
                                <div>
                                  <label className="text-xs font-medium text-pink-400 uppercase tracking-wider">
                                    GPU Time
                                  </label>
                                  <p className="text-pink-400 font-semibold">
                                    {task.metrics.resource_usage.gpu_time_sec.toFixed(2)}s
                                  </p>
                                </div>
                              )}
                            </div>

                            {/* Custom Metrics */}
                            {task.metrics?.custom_metrics && Object.keys(task.metrics.custom_metrics).length > 0 && (
                              <div className="mt-3 pt-3 border-t border-gray-600">
                                <h6 className="text-xs font-medium text-gray-400 uppercase tracking-wider mb-2">
                                  Custom Metrics
                                </h6>
                                <div className="grid grid-cols-2 md:grid-cols-3 gap-2">
                                  {Object.entries(task.metrics.custom_metrics).map(([key, value]) => (
                                    <div key={key}>
                                      <label className="text-xs text-gray-500 capitalize">{key.replace(/_/g, ' ')}</label>
                                      <p className="text-teal-400 font-medium text-sm">
                                        {typeof value === 'number' ? value.toLocaleString() : String(value)}
                                      </p>
                                    </div>
                                  ))}
                                </div>
                              </div>
                            )}
                          </div>

                          {/* Task Results Section */}
                          {task.results && (
                            <div className="mt-4 pt-3 border-t border-gray-600">
                              <h5 className="text-sm font-medium text-gray-300 mb-3">
                                Task Results
                              </h5>
                              <div className="bg-black/30 border border-white/10 rounded-md p-3 font-mono text-xs whitespace-pre-wrap max-h-48 overflow-auto">
                                {typeof task.results === 'string' ? 
                                  task.results : 
                                  JSON.stringify(task.results, null, 2)
                                }
                              </div>
                            </div>
                          )}
                        </div>
                        {task.failure_reason && (
                          <div className="mt-3 pt-3 border-t border-white/10">
                            <label className="text-xs font-medium text-gray-400 uppercase tracking-wider">
                              Failure Reason
                            </label>
                            <p className="text-red-400 text-sm">
                              {typeof task.failure_reason === "object"
                                ? task.failure_reason.kind
                                : String(task.failure_reason)}
                            </p>
                          </div>
                        )}
                        <div className="mt-4 pt-3 border-t border-white/10">
                          <button
                            type="button"
                            disabled={loadingLogs === `${task.run_id}-${task.task_id}`}
                            onClick={(e) => {
                              e.stopPropagation();
                              openCodeModal(task);
                            }}
                            className={cn(
                              "cursor-pointer inline-flex items-center px-4 py-2 border rounded-lg text-sm font-medium transition-colors duration-200",
                              loadingLogs === `${task.run_id}-${task.task_id}`
                                ? "bg-gray-500/10 border-gray-500/30 text-gray-500 cursor-not-allowed"
                                : "bg-blue-500/10 hover:bg-blue-500/20 border-blue-500/30 text-blue-400"
                            )}
                          >
                            {loadingLogs === `${task.run_id}-${task.task_id}` ? (
                              <div className="animate-spin rounded-full h-4 w-4 mr-2 border-b-2 border-gray-500"></div>
                            ) : (
                              <svg className="h-4 w-4 mr-2" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M10 20l4-16m4 4l4 4-4 4M6 16l-4-4 4-4" />
                              </svg>
                            )}
                            {loadingLogs === `${task.run_id}-${task.task_id}` ? 'Loading...' : 'View Logs'}
                          </button>
                        </div>
                      </div>
                    ))}
                    </div>
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
      />
    </>
  );
};

export default AgentDetails;
