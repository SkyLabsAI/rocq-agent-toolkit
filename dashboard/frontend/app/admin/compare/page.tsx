"use client";

import React, { useMemo, useState, Suspense, useEffect } from "react";
import type { TaskOutput, RunDetailsResponse } from "@/types/types";
import Link from "next/link";
import cn from "classnames";
import { useSearchParams } from "next/navigation";
import { getRunDetails } from "@/services/dataservice";

interface RunStats {
  id: string;
  name: string;
  tasks: number;
  successRate: number;
  totalLlmCalls: number;
  totalTokens: number;
  avgExecutionTime: number;
}

interface RunTaskCell { 
  run: RunDetailsResponse; 
  task?: TaskOutput;
}

const computeRunStats = (run: RunDetailsResponse): RunStats => {
  const tasks = run.tasks.length;
  const successes = run.tasks.filter(t => t.status === 'Success').length;
  return {
    id: run.run_id,
    name: run.agent_name,
    tasks,
    successRate: tasks === 0 ? 0 : successes / tasks,
    totalLlmCalls: run.tasks.reduce((a, t) => a + (t.metrics?.llm_invocation_count || 0), 0),
    totalTokens: run.tasks.reduce((a, t) => a + (t.metrics?.token_counts?.total_tokens || 0), 0),
    avgExecutionTime: tasks === 0 ? 0 : run.tasks.reduce((a, t) => a + (t.metrics?.resource_usage?.execution_time_sec || 0), 0) / tasks
  };
};

const normalizeFailureReason = (fr: unknown): string => {
  if (fr == null) return '';
  if (Array.isArray(fr)) {
    return fr.map(x => typeof x === 'string' ? x : JSON.stringify(x)).join(' | ');
  }
  if (typeof fr === "object") {
    const obj = fr as { kind?: string; value?: unknown };
    if (obj.kind) {
      return obj.kind + (obj.value ? ": " + (typeof obj.value === "object" ? JSON.stringify(obj.value) : String(obj.value)) : "");
    }
    return JSON.stringify(fr);
  }
  return String(fr);
};

const ComparePageContent: React.FC = () => {
  const sp = useSearchParams();
  const agentName = sp.get("agent") || "";
  const runsParam = sp.get("runs") || "";
  
  const runIds = useMemo(() => {
    return runsParam.split(",").map(r => r.trim()).filter(Boolean);
  }, [runsParam]);
  
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [selectedRuns, setSelectedRuns] = useState<RunDetailsResponse[]>([]);
  
  useEffect(() => {
    const fetchRunDetails = async () => {
      if (runIds.length === 0) {
        setLoading(false);
        return;
      }

      setLoading(true);
      setError(null);
      
      try {
        const runDetails = await getRunDetails(runIds);
        setSelectedRuns(runDetails);
      } catch (err) {
        console.error('Error fetching run details:', err);
        setError(err instanceof Error ? err.message : 'Failed to fetch run details');
        setSelectedRuns([]);
      } finally {
        setLoading(false);
      }
    };

    fetchRunDetails();
  }, [runIds]);
  
  const stats = useMemo(() => selectedRuns.map(computeRunStats), [selectedRuns]);

  const taskMap = useMemo(() => {
    const map: Record<string, RunTaskCell[]> = {};
    selectedRuns.forEach((run, runIdx) => {
      run.tasks.forEach(task => {
        if (!map[task.task_id]) {
          map[task.task_id] = selectedRuns.map(r => ({ run: r, task: undefined }));
        }
        map[task.task_id][runIdx] = { run, task };
      });
    });
    return map;
  }, [selectedRuns]);

  const [showTasks, setShowTasks] = useState(true);
  const [selectedTaskId, setSelectedTaskId] = useState<string | null>(null);
  const allTaskIds = useMemo(() => Object.keys(taskMap).sort(), [taskMap]);
  
  const selectTask = (taskId: string) => {
    setSelectedTaskId(prev => prev === taskId ? null : taskId);
  };

  return (
    <div className="min-h-screen bg-linear-to-b from-gray-950 to-gray-900 text-white p-8">
      <div className="max-w-7xl mx-auto space-y-8">
        {/* Header */}
        <div className="flex items-center justify-between flex-wrap gap-4">
          <div>
            <h1 className="text-2xl font-bold tracking-tight">Compare Runs</h1>
            <p className="text-sm text-gray-400 mt-1">
              {agentName ? `Agent: ${agentName}` : 'No agent specified'}
            </p>
          </div>
          <Link 
            href="/admin" 
            className="inline-flex items-center px-4 py-2 rounded-md bg-blue-500/10 hover:bg-blue-500/20 border border-blue-500/30 text-blue-300 text-sm font-medium transition-colors"
          >
            ← Back
          </Link>
        </div>

        {/* Loading state */}
        {loading && runIds.length > 0 && (
          <div className="border border-white/10 rounded-lg p-8 text-center">
            <div className="flex items-center justify-center mb-4">
              <div className="animate-spin rounded-full h-8 w-8 border-b-2 border-blue-400"></div>
            </div>
            <p className="text-gray-400">Loading run comparison data...</p>
          </div>
        )}

        {/* Error state */}
        {error && (
          <div className="border border-red-500/30 bg-red-500/5 rounded-lg p-6 text-center">
            <div className="flex items-center justify-center mb-3">
              <svg className="h-8 w-8 text-red-400" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-2.5L13.732 4c-.77-.833-1.964-.833-2.732 0L3.732 16.5c-.77.833.192 2.5 1.732 2.5z" />
              </svg>
            </div>
            <h4 className="text-red-300 font-medium mb-2">Failed to Load Run Data</h4>
            <p className="text-red-200 text-sm mb-4">{error}</p>
            <button
              onClick={() => window.location.reload()}
              className="px-4 py-2 bg-red-500/20 hover:bg-red-500/30 border border-red-500/40 text-red-300 rounded-lg text-sm font-medium transition-colors"
            >
              Try Again
            </button>
          </div>
        )}

        {/* No runs state */}
        {!loading && runIds.length === 0 && (
          <div className="border border-white/10 rounded-lg p-8 text-center">
            <p className="text-gray-400">
              No runs specified. Select runs from an agent&apos;s details and click Compare Selected.
            </p>
          </div>
        )}

        {/* Runs not found state */}
        {!loading && !error && runIds.length > 0 && selectedRuns.length === 0 && (
          <div className="border border-yellow-500/30 bg-yellow-500/5 rounded-lg p-6">
            <p className="text-yellow-300 text-sm">
              No runs were found with the specified IDs.
            </p>
          </div>
        )}

        {/* Main content */}
        {!loading && !error && stats.length > 0 && (
          <div className="space-y-6">
            {/* Run stats table */}
            <div className="overflow-x-auto rounded-lg border border-white/10">
              <table className="min-w-full divide-y divide-white/10">
                <thead className="bg-white/5">
                  <tr>
                    {['Run ID', 'Name', 'Tasks', 'Success %', 'LLM Calls', 'Total Tokens', 'Avg Exec Time (s)'].map(head => (
                      <th 
                        key={head} 
                        className="px-4 py-3 text-left text-xs font-semibold text-gray-300 uppercase tracking-wider"
                      >
                        {head}
                      </th>
                    ))}
                  </tr>
                </thead>
                <tbody className="divide-y divide-white/10">
                  {stats.map(s => (
                    <tr key={s.id} className="hover:bg-white/5 transition-colors">
                      <td className="px-4 py-3 font-mono text-xs truncate max-w-40" title={s.id}>
                        {s.id}
                      </td>
                      <td className="px-4 py-3 text-sm truncate max-w-[220px]" title={s.name}>
                        {s.name}
                      </td>
                      <td className="px-4 py-3 text-sm">{s.tasks}</td>
                      <td className="px-4 py-3 text-sm">
                        <span className={cn(
                          "px-2 py-0.5 rounded-full text-xs font-medium",
                          s.successRate >= 0.7 ? 'bg-green-500/20 text-green-300 border border-green-500/30' :
                          s.successRate >= 0.4 ? 'bg-yellow-500/20 text-yellow-300 border border-yellow-500/30' :
                          'bg-red-500/20 text-red-300 border border-red-500/30'
                        )}>
                          {(s.successRate * 100).toFixed(1)}%
                        </span>
                      </td>
                      <td className="px-4 py-3 text-sm">{s.totalLlmCalls}</td>
                      <td className="px-4 py-3 text-sm">{s.totalTokens.toLocaleString()}</td>
                      <td className="px-4 py-3 text-sm">{s.avgExecutionTime.toFixed(2)}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>

            {/* Delta comparison for 2 runs */}
            {/* {stats.length === 2 && (
              <div className="grid md:grid-cols-2 gap-6">
                {(['successRate', 'totalLlmCalls', 'totalTokens', 'avgExecutionTime'] as const).map(metric => {
                  const a = stats[0];
                  const b = stats[1];
                  const diff = b[metric] - a[metric];
                  const isRate = metric === 'successRate';
                  const metricLabel = {
                    successRate: 'Success Rate Δ',
                    totalLlmCalls: 'LLM Calls Δ',
                    totalTokens: 'Total Tokens Δ',
                    avgExecutionTime: 'Avg Exec Time Δ'
                  }[metric];

                  return (
                    <div key={metric} className="border border-white/10 rounded-lg p-4 bg-white/5">
                      <h3 className="text-sm font-semibold mb-2 text-gray-200">{metricLabel}</h3>
                      <div className="flex items-baseline gap-3">
                        <span className="text-xs text-gray-400 font-mono truncate" title={a.id}>
                          {a.id}
                        </span>
                        <span className="text-sm font-medium">→</span>
                        <span className="text-xs text-gray-400 font-mono truncate" title={b.id}>
                          {b.id}
                        </span>
                      </div>
                      <div className="mt-2 text-lg font-semibold">
                        {isRate ? (diff * 100).toFixed(2) + '%' : diff.toFixed(2)}
                        <span className="ml-2 text-xs font-medium px-2 py-0.5 rounded-full bg-purple-500/20 text-purple-300 border border-purple-500/30">
                          Δ
                        </span>
                      </div>
                      <p className="text-xs text-gray-400 mt-2">
                        Positive means second run higher.
                      </p>
                    </div>
                  );
                })}
              </div>
            )} */}

            {/* Per-task comparison */}
            {selectedRuns.length > 1 && (
              <div className="space-y-4">
                <div className="flex items-center justify-between">
                  <h2 className="text-lg font-semibold tracking-tight">Taskwise comparison</h2>
                  <button 
                    onClick={() => setShowTasks(s => !s)} 
                    className="px-3 py-1.5 rounded-md text-sm bg-purple-500/20 hover:bg-purple-500/30 border border-purple-500/40 text-purple-200"
                  >
                    {showTasks ? 'Hide' : 'Show'}
                  </button>
                </div>
                
                {showTasks && (
                  <div className="overflow-x-auto rounded-lg border border-white/10">
                    <table className="min-w-full divide-y divide-white/10 text-sm">
                      <thead className="bg-white/5">
                        <tr>
                          <th className="px-4 py-3 text-left text-xs font-semibold uppercase tracking-wider text-gray-300">
                            Task ID
                          </th>
                          {selectedRuns.map(r => (
                            <th key={r.run_id} className="px-4 py-3 text-left text-xs font-semibold uppercase tracking-wider text-gray-300">
                              <span className="font-mono block truncate" title={r.run_id}>{r.run_id}</span>
                            </th>
                          ))}
                        </tr>
                      </thead>
                      <tbody className="divide-y divide-white/10">
                        {allTaskIds.map(taskId => {
                          const row = taskMap[taskId];
                          return (
                            <tr 
                              key={taskId} 
                              className={cn(
                                "transition-colors", 
                                selectedTaskId === taskId ? 
                                  "bg-purple-500/10 hover:bg-purple-500/20" : 
                                  "hover:bg-white/5"
                              )}
                            > 
                              <td 
                                className="px-4 py-3 align-top cursor-pointer" 
                                onClick={() => selectTask(taskId)}
                              >
                                <div className="space-y-1">
                                  <p className="font-mono text-xs truncate max-w-56" title={taskId}>
                                    {taskId}
                                  </p>
                                  {selectedTaskId === taskId && (
                                    <span className="text-[10px] text-purple-300">Split view ↓</span>
                                  )}
                                </div>
                              </td>
                              {row.map((runCell, idx) => {
                                const t = runCell.task;
                                if (!t) {
                                  return (
                                    <td key={idx} className="px-4 py-3 text-xs text-gray-500 italic">
                                      –
                                    </td>
                                  );
                                }
                                const statusColor = t.status === 'Success' ? 
                                  'bg-green-500/20 text-green-300 border-green-500/30' : 
                                  'bg-red-500/20 text-red-300 border-red-500/30';
                                
                                return (
                                  <td key={idx} className="px-4 py-3 align-top">
                                    <div className="space-y-1">
                                      <span className={cn(
                                        'px-2 py-0.5 rounded-full text-[10px] font-semibold border inline-block', 
                                        statusColor
                                      )}>
                                        {t.status}
                                      </span>
                                      <div className="grid grid-cols-2 gap-1 mt-1 text-xs">
                                        {/* LLM Metrics */}
                                        <div className="col-span-2 mb-1">
                                          <p className="text-[9px] text-blue-400 font-semibold">LLM METRICS</p>
                                        </div>
                                        <div>
                                          <p className="text-[10px] text-gray-400">Calls</p>
                                          <p className="text-xs font-medium text-blue-300">
                                            {t.metrics?.llm_invocation_count ?? '-'}
                                          </p>
                                        </div>
                                        <div>
                                          <p className="text-[10px] text-gray-400">Total Tokens</p>
                                          <p className="text-xs font-medium text-purple-300">
                                            {t.metrics?.token_counts?.total_tokens?.toLocaleString() ?? '-'}
                                          </p>
                                        </div>
                                        <div>
                                          <p className="text-[10px] text-gray-400">Input Tokens</p>
                                          <p className="text-xs font-medium text-purple-200">
                                            {t.metrics?.token_counts?.input_tokens?.toLocaleString() ?? '-'}
                                          </p>
                                        </div>
                                        <div>
                                          <p className="text-[10px] text-gray-400">Output Tokens</p>
                                          <p className="text-xs font-medium text-purple-200">
                                            {t.metrics?.token_counts?.output_tokens?.toLocaleString() ?? '-'}
                                          </p>
                                        </div>
                                        
                                        {/* Resource Usage */}
                                        <div className="col-span-2 mt-2 mb-1">
                                          <p className="text-[9px] text-orange-400 font-semibold">RESOURCE USAGE</p>
                                        </div>
                                        <div>
                                          <p className="text-[10px] text-gray-400">Exec Time (s)</p>
                                          <p className="text-xs font-medium text-orange-300">
                                            {t.metrics?.resource_usage?.execution_time_sec?.toFixed(2) ?? '-'}
                                          </p>
                                        </div>
                                        <div>
                                          <p className="text-[10px] text-gray-400">CPU Time (s)</p>
                                          <p className="text-xs font-medium text-orange-200">
                                            {t.metrics?.resource_usage?.cpu_time_sec?.toFixed(2) ?? '-'}
                                          </p>
                                        </div>
                                        <div>
                                          <p className="text-[10px] text-gray-400">GPU Time (s)</p>
                                          <p className="text-xs font-medium text-orange-200">
                                            {t.metrics?.resource_usage?.gpu_time_sec?.toFixed(2) ?? '-'}
                                          </p>
                                        </div>
                                        
                                        {/* Timestamp */}
                                        <div>
                                          <p className="text-[10px] text-gray-400">Timestamp</p>
                                          <p className="text-xs font-medium text-gray-300" title={t.timestamp_utc}>
                                            {new Date(t.timestamp_utc).toLocaleTimeString()}
                                          </p>
                                        </div>
                                        
                                        {/* Custom Metrics */}
                                        {t.metrics?.custom && Object.keys(t.metrics.custom).length > 0 && (
                                          <>
                                            <div className="col-span-2 mt-2 mb-1">
                                              <p className="text-[9px] text-green-400 font-semibold">CUSTOM METRICS</p>
                                            </div>
                                            {Object.entries(t.metrics.custom).slice(0, 4).map(([key, value]) => (
                                              <div key={key}>
                                                <p className="text-[10px] text-gray-400 truncate" title={key}>{key}</p>
                                                <p className="text-xs font-medium text-green-300 truncate" title={String(value)}>
                                                  {typeof value === 'number' ? value.toLocaleString() : String(value)}
                                                </p>
                                              </div>
                                            ))}
                                          </>
                                        )}
                                      </div>
                                      {t.failure_reason && (
                                        <p 
                                          className="text-[10px] text-red-300 mt-1 truncate" 
                                          title={normalizeFailureReason(t.failure_reason)}
                                        >
                                          {normalizeFailureReason(t.failure_reason)}
                                        </p>
                                      )}
                                    </div>
                                  </td>
                                );
                              })}
                            </tr>
                          );
                        })}
                      </tbody>
                    </table>
                  </div>
                )}

                {/* Split view */}
                {selectedTaskId && (
                  <div className="mt-8 space-y-4">
                    <div className="flex items-center justify-between">
                      <h3 className="text-md font-semibold">
                        Split View: <span className="font-mono text-purple-300">{selectedTaskId}</span>
                      </h3>
                      <button 
                        onClick={() => setSelectedTaskId(null)} 
                        className="text-xs px-2 py-1 rounded-md bg-red-500/20 hover:bg-red-500/30 border border-red-500/40 text-red-200"
                      >
                        Close
                      </button>
                    </div>
                    <div 
                      className="grid gap-4" 
                      style={{ gridTemplateColumns: `repeat(${selectedRuns.length}, minmax(0,1fr))` }}
                    >
                        {selectedRuns.map((run, idx) => {
                        const cell = taskMap[selectedTaskId]?.[idx];
                        const task = cell?.task;
                        
                        return (
                          <div key={run.run_id} className="border border-white/10 rounded-lg bg-white/5 p-4 flex flex-col">
                            <div className="flex items-center justify-between mb-2">
                              <h4 className="text-sm font-medium truncate" title={run.agent_name}>
                                {run.agent_name}
                              </h4>
                              <span className="font-mono text-[10px] text-gray-400" title={run.run_id}>
                                {run.run_id}
                              </span>
                            </div>                            {!task ? (
                              <div className="text-xs text-gray-500 italic">
                                Task not present in this run.
                              </div>
                            ) : (
                              <div className="space-y-3">
                                <div className="flex items-center gap-2 flex-wrap">
                                  <span className={cn(
                                    'px-2 py-0.5 rounded-full text-[10px] font-semibold border', 
                                    task.status === 'Success' ? 
                                      'bg-green-500/20 text-green-300 border-green-500/30' : 
                                      'bg-red-500/20 text-red-300 border-red-500/30'
                                  )}>
                                    {task.status}
                                  </span>
                                  {task.failure_reason && (
                                    <span 
                                      className="text-[10px] text-red-300 truncate" 
                                      title={normalizeFailureReason(task.failure_reason)}
                                    >
                                      {normalizeFailureReason(task.failure_reason)}
                                    </span>
                                  )}
                                </div>
                                {/* LLM Metrics Section */}
                                <div className="space-y-2">
                                  <h5 className="text-blue-400 text-xs font-medium">LLM Metrics</h5>
                                  <div className="grid grid-cols-2 gap-2 text-xs">
                                    <div>
                                      <p className="text-gray-400">LLM Calls</p>
                                      <p className="font-medium">{task.metrics.llm_invocation_count}</p>
                                    </div>
                                    <div>
                                      <p className="text-gray-400">Total Tokens</p>
                                      <p className="font-medium">{task.metrics.token_counts.total_tokens.toLocaleString()}</p>
                                    </div>
                                    <div>
                                      <p className="text-gray-400">Input Tokens</p>
                                      <p className="font-medium">{task.metrics.token_counts.input_tokens.toLocaleString()}</p>
                                    </div>
                                    <div>
                                      <p className="text-gray-400">Output Tokens</p>
                                      <p className="font-medium">{task.metrics.token_counts.output_tokens.toLocaleString()}</p>
                                    </div>
                                  </div>
                                </div>

                                {/* Resource Usage Section */}
                                <div className="space-y-2">
                                  <h5 className="text-orange-400 text-xs font-medium">Resource Usage</h5>
                                  <div className="grid grid-cols-2 gap-2 text-xs">
                                    <div>
                                      <p className="text-gray-400">Exec Time (s)</p>
                                      <p className="font-medium">{task.metrics.resource_usage.execution_time_sec.toFixed(2)}</p>
                                    </div>
                                    {task.metrics.resource_usage.cpu_time_sec !== undefined && (
                                      <div>
                                        <p className="text-gray-400">CPU Time (s)</p>
                                        <p className="font-medium">{task.metrics.resource_usage.cpu_time_sec.toFixed(2)}</p>
                                      </div>
                                    )}
                                    {task.metrics.resource_usage.gpu_time_sec !== undefined && (
                                      <div>
                                        <p className="text-gray-400">GPU Time (s)</p>
                                        <p className="font-medium">{task.metrics.resource_usage.gpu_time_sec.toFixed(2)}</p>
                                      </div>
                                    )}
                                  </div>
                                </div>

                                {/* Timestamps */}
                                <div className="space-y-2">
                                  <h5 className="text-gray-400 text-xs font-medium">Timestamps</h5>
                                  <div className="grid grid-cols-1 gap-1 text-xs">
                                    {task.metrics.timestamp && (
                                      <div>
                                        <p className="text-gray-500">Completed</p>
                                        <p className="font-mono text-[10px]">{new Date(task.metrics.timestamp).toLocaleString()}</p>
                                      </div>
                                    )}
                                  </div>
                                </div>

                                {/* Custom Metrics */}
                                {task.metrics.custom_metrics && Object.keys(task.metrics.custom_metrics).length > 0 && (
                                  <div className="space-y-2">
                                    <h5 className="text-green-400 text-xs font-medium">Custom Metrics</h5>
                                    <div className="grid grid-cols-2 gap-2 text-xs">
                                      {Object.entries(task.metrics.custom_metrics).map(([key, value]) => (
                                        <div key={key}>
                                          <p className="text-gray-400 capitalize">{key.replace(/_/g, ' ')}</p>
                                          <p className="font-medium">
                                            {typeof value === 'number' ? value.toLocaleString() : String(value)}
                                          </p>
                                        </div>
                                      ))}
                                    </div>
                                  </div>
                                )}
                                {task.results && (
                                  <div className="text-[11px] bg-black/30 border border-white/10 rounded-md p-2 font-mono whitespace-pre-wrap max-h-48 overflow-auto">
                                    {typeof task.results === 'string' ? 
                                      (task.results as string).slice(0, 1200) : 
                                      JSON.stringify(task.results, null, 2)
                                    }
                                  </div>
                                )}
                              </div>
                            )}
                          </div>
                        );
                      })}
                    </div>
                  </div>
                )}
              </div>
            )}
          </div>
        )}
      </div>
    </div>
  );
};

const ComparePage: React.FC = () => {
  return (
    <Suspense fallback={
      <div className="min-h-screen bg-linear-to-b from-gray-950 to-gray-900 text-white p-8">
        <div className="max-w-7xl mx-auto">
          <div className="flex items-center justify-center h-64">
            <div className="text-gray-400">Loading comparison data...</div>
          </div>
        </div>
      </div>
    }>
      <ComparePageContent />
    </Suspense>
  );
};

export default ComparePage;
