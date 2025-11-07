"use client";

import Layout from "@/layouts/common";
import { getData } from "@/services/dataservice";
import { AgentResultsArray, AgentSummary } from "@/types/types";
import { useEffect, useState } from "react";
import AgentDetails from "../leaderboard/agentDetails";

const AdminDashboard: React.FC = () => {
  const [agentData, setAgentData] = useState<AgentSummary[]>([]);

  useEffect(() => {
    async function fetchData() {
      const data = await getData();
      setAgentData(data);
    }
    fetchData();
  }, []);

  return (
    <Layout title="Internal Dashboard">
   

      {/* Main Table */}
      <div className="bg-white/5 backdrop-blur-sm border border-white/10 rounded-xl overflow-hidden">
        <div className="px-6 py-4 border-b border-white/10">
          <h2 className="text-xl font-semibold text-white">
            Agent Performance
          </h2>
          <p className="text-gray-400 text-sm mt-1">
            Click on any row to view detailed task information
          </p>
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
