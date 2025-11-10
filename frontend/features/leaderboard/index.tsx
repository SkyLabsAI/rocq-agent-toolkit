"use client";

import Layout from "@/layouts/common";
import { getData } from "@/services/dataservice";
import {  AgentSummary } from "@/types/types";
import { useEffect, useState } from "react";
import AgentDetails from "./agentDetails";

const Leaderboard: React.FC = () => {
  const [agentData, setAgentData] = useState<AgentSummary[]>([]);


  useEffect(() => {
    async function fetchData() {
      const data = await getData();
      setAgentData(data);
    }
    fetchData();
  }, []);

  return (
    <Layout title="Leaderboard">
      {/* Stats Cards */}
      {/* <div className="grid grid-cols-1 md:grid-cols-4 gap-6 mb-8">
        <div className="bg-white/5 backdrop-blur-sm border border-white/10 rounded-xl p-6">
          <div className="flex items-center justify-between">
            <div>
              <p className="text-sm font-medium text-gray-400">Total Agents</p>
              <p className="text-2xl font-bold text-white">{agentData.length}</p>
            </div>
            <div className="h-12 w-12 bg-blue-500/20 rounded-lg flex items-center justify-center">
              <svg className="h-6 w-6 text-blue-400" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M17 20h5v-2a3 3 0 00-5.356-1.857M17 20H7m10 0v-2c0-.656-.126-1.283-.356-1.857M7 20H2v-2a3 3 0 015.356-1.857M7 20v-2c0-.656.126-1.283.356-1.857m0 0a5.002 5.002 0 019.288 0M15 7a3 3 0 11-6 0 3 3 0 016 0zm6 3a2 2 0 11-4 0 2 2 0 014 0zM7 10a2 2 0 11-4 0 2 2 0 014 0z" />
              </svg>
            </div>
          </div>
        </div>

        <div className="bg-white/5 backdrop-blur-sm border border-white/10 rounded-xl p-6">
          <div className="flex items-center justify-between">
            <div>
              <p className="text-sm font-medium text-gray-400">Avg Success Rate</p>
              <p className="text-2xl font-bold text-green-400">
                {agentData.length > 0 ? ((agentData.reduce((sum, agent) => sum + agent.avgSuccessRate, 0) / agentData.length) * 100).toFixed(1) : 0}%
              </p>
            </div>
            <div className="h-12 w-12 bg-green-500/20 rounded-lg flex items-center justify-center">
              <svg className="h-6 w-6 text-green-400" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z" />
              </svg>
            </div>
          </div>
        </div>

        <div className="bg-white/5 backdrop-blur-sm border border-white/10 rounded-xl p-6">
          <div className="flex items-center justify-between">
            <div>
              <p className="text-sm font-medium text-gray-400">Verified Agents</p>
              <p className="text-2xl font-bold text-purple-400">
                {agentData.filter(agent => agent.verified).length}
              </p>
            </div>
            <div className="h-12 w-12 bg-purple-500/20 rounded-lg flex items-center justify-center">
              <svg className="h-6 w-6 text-purple-400" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 12l2 2 4-4M7.835 4.697a3.42 3.42 0 001.946-.806 3.42 3.42 0 014.438 0 3.42 3.42 0 001.946.806 3.42 3.42 0 013.138 3.138 3.42 3.42 0 00.806 1.946 3.42 3.42 0 010 4.438 3.42 3.42 0 00-.806 1.946 3.42 3.42 0 01-3.138 3.138 3.42 3.42 0 00-1.946.806 3.42 3.42 0 01-4.438 0 3.42 3.42 0 00-1.946-.806 3.42 3.42 0 01-3.138-3.138 3.42 3.42 0 00-.806-1.946 3.42 3.42 0 010-4.438 3.42 3.42 0 00.806-1.946 3.42 3.42 0 013.138-3.138z" />
              </svg>
            </div>
          </div>
        </div>

        <div className="bg-white/5 backdrop-blur-sm border border-white/10 rounded-xl p-6">
          <div className="flex items-center justify-between">
            <div>
              <p className="text-sm font-medium text-gray-400">Total Tasks</p>
              <p className="text-2xl font-bold text-orange-400">
                {agentData.reduce((sum, agent) => sum + agent.tasksAttempted, 0)}
              </p>
            </div>
            <div className="h-12 w-12 bg-orange-500/20 rounded-lg flex items-center justify-center">
              <svg className="h-6 w-6 text-orange-400" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 5H7a2 2 0 00-2 2v10a2 2 0 002 2h8a2 2 0 002-2V7a2 2 0 00-2-2h-2M9 5a2 2 0 002 2h2a2 2 0 002-2M9 5a2 2 0 012-2h2a2 2 0 012 2" />
              </svg>
            </div>
          </div>
        </div>
      </div> */}

      {/* Main Table */}
      <div className="bg-white/5 backdrop-blur-sm border border-white/10 rounded-xl overflow-hidden">
        <div className="px-6 py-4 border-b border-white/10">
          <h2 className="text-xl font-semibold text-white">Agent Performance</h2>
          <p className="text-gray-400 text-sm mt-1">Click on any row to view detailed task information</p>
        </div>
        
        <div className="overflow-x-auto">
          <table className="w-full text-left border-collapse">
            <thead className="bg-white/5">
              <tr>
                <th className="px-6 py-4 text-xs font-medium text-gray-400 uppercase tracking-wider">Agent Name</th>
                <th className="px-6 py-4 text-xs font-medium text-gray-400 uppercase tracking-wider">Verified</th>
                <th className="px-6 py-4 text-xs font-medium text-gray-400 uppercase tracking-wider">Organization</th>
                <th className="px-6 py-4 text-xs font-medium text-gray-400 uppercase tracking-wider">Success Rate</th>
                <th className="px-6 py-4 text-xs font-medium text-gray-400 uppercase tracking-wider">Avg Time (s)</th>
                <th className="px-6 py-4 text-xs font-medium text-gray-400 uppercase tracking-wider">Avg Tokens</th>
                <th className="px-6 py-4 text-xs font-medium text-gray-400 uppercase tracking-wider">Avg LLM Calls</th>
              </tr>
            </thead>
            <tbody className="divide-y divide-white/10">
              {agentData.map((agent) => (
                <AgentDetails key={agent.agent_name} agent_name={agent.agent_name} />
              ))}
            </tbody>
          </table>
        </div>
      </div>
    </Layout>
  );
};

export default Leaderboard;
