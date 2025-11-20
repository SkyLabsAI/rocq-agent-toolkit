import React from 'react';
import TaskButton from '@/components/base/taskButton';
import cn from 'classnames';

interface AgentTasksViewProps {
  taskDetails: any[];
  loadingLogs: string | null;
  openCodeModal: (task: any) => void;
}

const AgentTasksView: React.FC<AgentTasksViewProps> = ({ taskDetails, loadingLogs, openCodeModal }) => {
  return (
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
                  {typeof task.task_kind === 'object'
                    ? task.task_kind.kind +
                      ('value' in task.task_kind ? ` (${task.task_kind.value})` : '')
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
                    {task.metrics?.llm_invocation_count ?? '-'}
                  </p>
                </div>
                <div>
                  <label className="text-xs font-medium text-purple-400 uppercase tracking-wider">
                    Total Tokens
                  </label>
                  <p className="text-purple-400 font-bold text-lg">
                    {task.metrics?.token_counts?.total_tokens?.toLocaleString() ?? '-'}
                  </p>
                </div>
                <div>
                  <label className="text-xs font-medium text-green-400 uppercase tracking-wider">
                    Input Tokens
                  </label>
                  <p className="text-green-400 font-semibold">
                    {task.metrics?.token_counts?.input_tokens?.toLocaleString() ?? '-'}
                  </p>
                </div>
                <div>
                  <label className="text-xs font-medium text-orange-400 uppercase tracking-wider">
                    Output Tokens
                  </label>
                  <p className="text-orange-400 font-semibold">
                    {task.metrics?.token_counts?.output_tokens?.toLocaleString() ?? '-'}
                  </p>
                </div>
                <div>
                  <label className="text-xs font-medium text-red-400 uppercase tracking-wider">
                    Execution Time
                  </label>
                  <p className="text-red-400 font-bold text-lg">
                    {task.metrics?.resource_usage?.execution_time_sec?.toFixed(2) ?? '-'}s
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
                <h5 className="text-sm font-medium text-gray-300 mb-3">Task Results</h5>
                <div className="bg-black/30 border border-white/10 rounded-md p-3 font-mono text-xs whitespace-pre-wrap max-h-48 overflow-auto">
                  {typeof task.results === 'string'
                    ? task.results
                    : JSON.stringify(task.results, null, 2)}
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
                {Array.isArray(task.failure_reason)
                  ? task.failure_reason.join(', ')
                  : typeof task.failure_reason === 'object' && task.failure_reason !== null && 'kind' in task.failure_reason
                  ? (task.failure_reason as any).kind
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
                'cursor-pointer inline-flex items-center px-4 py-2 border rounded-lg text-sm font-medium transition-colors duration-200',
                loadingLogs === `${task.run_id}-${task.task_id}`
                  ? 'bg-gray-500/10 border-gray-500/30 text-gray-500 cursor-not-allowed'
                  : 'bg-blue-500/10 hover:bg-blue-500/20 border-blue-500/30 text-blue-400'
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
  );
};

export default AgentTasksView;