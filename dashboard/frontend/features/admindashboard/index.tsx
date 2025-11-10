"use client";

import Layout from "@/layouts/common";
import AgentDetails from "../leaderboard/agentDetails";
import { useAdminDashboard } from "@/hooks/useAdminDashboard";

const AdminDashboard: React.FC = () => {
  const { agentData, isRefreshing, refreshMessage, handleRefresh } = useAdminDashboard();

  return (
    <Layout title="Internal Dashboard">
      {/* Refresh Message */}
      {refreshMessage && (
        <div className="mb-4 bg-white/5 backdrop-blur-sm border border-white/10 rounded-xl p-4">
          <p className="text-sm text-green-400">{refreshMessage}</p>
        </div>
      )}

      {/* Main Table */}
      <div className="bg-white/5 backdrop-blur-sm border border-white/10 rounded-xl overflow-hidden">
        <div className="px-6 py-4 border-b border-white/10 flex items-center justify-between">
          <div>
            <h2 className="text-xl font-semibold text-white">
              Agent Performance
            </h2>
            <p className="text-gray-400 text-sm mt-1">
              Click on any row to view detailed task information
            </p>
          </div>
          <button
            onClick={handleRefresh}
            disabled={isRefreshing}
            className="flex items-center gap-2 px-4 py-2 bg-blue-500/20 hover:bg-blue-500/30 border border-blue-400/30 rounded-lg text-blue-400 font-medium transition-all disabled:opacity-50 disabled:cursor-not-allowed"
          >
            <svg 
              className={`h-5 w-5 ${isRefreshing ? 'animate-spin' : ''}`} 
              fill="none" 
              viewBox="0 0 24 24" 
              stroke="currentColor"
            >
              <path 
                strokeLinecap="round" 
                strokeLinejoin="round" 
                strokeWidth={2} 
                d="M4 4v5h.582m15.356 2A8.001 8.001 0 004.582 9m0 0H9m11 11v-5h-.581m0 0a8.003 8.003 0 01-15.357-2m15.357 2H15" 
              />
            </svg>
            {isRefreshing ? 'Refreshing...' : 'Refresh Data'}
          </button>
        </div>

        <div className="overflow-x-auto">
          <table className="w-full text-left border-collapse">
            <thead className="bg-white/5">
              <tr>
                <th className="px-6 py-4 text-xs font-medium text-gray-400 uppercase tracking-wider">
                  Agent Name
                </th>
                {/* <th className="px-6 py-4 text-xs font-medium text-gray-400 uppercase tracking-wider">
                  Verified
                </th>
                <th className="px-6 py-4 text-xs font-medium text-gray-400 uppercase tracking-wider">
                  Organization
                </th>
                <th className="px-6 py-4 text-xs font-medium text-gray-400 uppercase tracking-wider">
                  Success Rate
                </th>
                <th className="px-6 py-4 text-xs font-medium text-gray-400 uppercase tracking-wider">
                  Avg Time (s)
                </th>
                <th className="px-6 py-4 text-xs font-medium text-gray-400 uppercase tracking-wider">
                  Avg Tokens
                </th>
                <th className="px-6 py-4 text-xs font-medium text-gray-400 uppercase tracking-wider">
                  Avg LLM Calls
                </th> */}
              </tr>
            </thead>
            <tbody className="divide-y divide-white/10">
              {agentData.map((agent) => (
                <AgentDetails key={agent.agent_name} agent_name={agent.agent_name} adminView />
              ))}
            </tbody>
          </table>
        </div>
      </div>
    </Layout>
  );
};

export default AdminDashboard;
