import React from 'react';
import TaskButton from "@/components/base/taskButton";
import { Button } from '@/components/base/Button';
import cn from "classnames";

interface AgentRunsViewProps {
  runDetails: any[];
  expandedRuns: Set<string>;
  selectedRuns: string[];
  loadingRunDetails: Set<string>;
  runTaskDetails: Map<string, any[]>;
  loadingLogs: string | null;
  toggleRunExpansion: (runId: string) => void;
  toggleRunSelection: (runId: string) => void;
  clearSelectedRuns: () => void;
  compareSelected: () => void;
  openCodeModal: (task: any) => void;
}

const AgentRunsView: React.FC<AgentRunsViewProps> = ({
  runDetails,
  expandedRuns,
  selectedRuns,
  loadingRunDetails,
  runTaskDetails,
  loadingLogs,
  toggleRunExpansion,
  toggleRunSelection,
  clearSelectedRuns,
  compareSelected,
  openCodeModal,
}) => {
  return (
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
                <Button
                  variant={selectedRuns.includes(run.run_id) ? 'default' : 'ghost'}
                  onClick={(e) => { e.stopPropagation(); toggleRunSelection(run.run_id); }}
                  className={cn(
                    "px-3 py-1 text-sm font-medium transition-colors",
                    selectedRuns.includes(run.run_id)
                      ? "bg-green-500/20 border-green-500/40 text-green-300 hover:bg-green-500/30"
                      : "bg-blue-500/10 border-blue-500/30 text-blue-300 hover:bg-blue-500/20"
                  )}
                >
                  {selectedRuns.includes(run.run_id) ? 'Selected' : 'Add to Compare'}
                </Button>
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
                      <Button
                        variant="ghost"
                        disabled={loadingLogs === `${task.run_id}-${task.task_id}`}
                        onClick={(e) => {
                          e.stopPropagation();
                          openCodeModal(task);
                        }}
                        className={cn(
                          "inline-flex items-center px-4 py-2 text-sm font-medium transition-colors duration-200",
                          loadingLogs === `${task.run_id}-${task.task_id}`
                            ? "bg-gray-500/10 border-gray-500/30 text-gray-500 cursor-not-allowed"
                            : "bg-blue-500/10 hover:bg-blue-500/20 border-blue-500/30 text-blue-400"
                        )}
                        leftIcon={
                          loadingLogs === `${task.run_id}-${task.task_id}` ? (
                            <div className="animate-spin rounded-full h-4 w-4 border-b-2 border-gray-500"></div>
                          ) : (
                            <svg className="h-4 w-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M10 20l4-16m4 4l4 4-4 4M6 16l-4-4 4-4" />
                            </svg>
                          )
                        }
                      >
                        {loadingLogs === `${task.run_id}-${task.task_id}` ? 'Loading...' : 'View Logs'}
                      </Button>
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
              <Button
                variant="ghost"
                onClick={(e) => { e.stopPropagation(); clearSelectedRuns(); }}
                className="px-3 py-2 text-sm bg-red-500/10 hover:bg-red-500/20 border-red-500/30 text-red-300"
              >
                Clear Selection
              </Button>
            )}
            <Button
              variant={selectedRuns.length < 2 ? 'ghost' : 'default'}
              disabled={selectedRuns.length < 2}
              onClick={(e) => { e.stopPropagation(); compareSelected(); }}
              className={cn(
                "px-4 py-2 text-sm font-medium transition-colors",
                selectedRuns.length < 2
                  ? "bg-gray-700 text-gray-400 border-gray-600 cursor-not-allowed"
                  : "bg-purple-500/20 border-purple-500/40 text-purple-300 hover:bg-purple-500/30"
              )}
            >
              {selectedRuns.length < 2 ? 'Select ≥ 2 runs' : 'Compare Selected'}
            </Button>
          </div>
        </div>
      )}
    </div>
  );
};

export default AgentRunsView;