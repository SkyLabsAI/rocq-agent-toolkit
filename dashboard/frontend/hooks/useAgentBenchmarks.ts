// import { useEffect, useState } from 'react';
// import { getBenchmarks, getBenchmarkAgents } from '@/services/dataservice';
// import { Benchmark, AgentSummary } from '@/types/types';
// import { Run } from '@/types/types';

// export interface AgentBenchmarkData {
//   benchmark: Benchmark;
//   runs: Run[];
// }

// export interface AgentWithBenchmarks extends AgentSummary {
//   benchmarks: AgentBenchmarkData[];
// }

// export const useAgentBenchmarks = () => {
//   const [agentsWithBenchmarks, setAgentsWithBenchmarks] = useState<AgentWithBenchmarks[]>([]);
//   const [isLoading, setIsLoading] = useState(true);
//   const [error, setError] = useState<string | null>(null);

//   const fetchAgentBenchmarkData = async () => {
//     setIsLoading(true);
//     setError(null);
    
//     try {
//       // 1. Get all benchmarks
//       const benchmarks = await getBenchmarks();
      
//       // 2. Get all agents data for each benchmark
//       const benchmarkAgentsData = await Promise.all(
//         benchmarks.map(async (benchmark) => {
//           const agentData = await getBenchmarkAgents(benchmark.dataset_id);
//           return { benchmark, agentData };
//         })
//       );
      
//       // 3. Group runs by agent across all benchmarks
//       const agentMap = new Map<string, AgentWithBenchmarks>();
      
//       benchmarkAgentsData.forEach(({ benchmark, agentData }) => {
//         agentData.agents.forEach((agent) => {
//           const agentName = agent.agent_name;
          
//           if (!agentMap.has(agentName)) {
//             // Initialize agent with benchmark data
//             agentMap.set(agentName, {
//               ...agent,
//               benchmarks: []
//             });
//           }
          
//           const agentWithBenchmarks = agentMap.get(agentName)!;
          
//           // Add runs for this benchmark
//           const benchmarkData: AgentBenchmarkData = {
//             benchmark,
//             runs: agent.runs
//           };
          
//           agentWithBenchmarks.benchmarks.push(benchmarkData);
//         });
//       });
      
//       // 4. Convert map to array and sort by agent name
//       const agentsArray = Array.from(agentMap.values()).sort((a, b) => 
//         a.agent_name.localeCompare(b.agent_name)
//       );
      
//       setAgentsWithBenchmarks(agentsArray);
//     } catch (err) {
//       console.error('Error fetching agent benchmark data:', err);
//       setError(err instanceof Error ? err.message : 'Failed to fetch data');
//     } finally {
//       setIsLoading(false);
//     }
//   };

//   useEffect(() => {
//     fetchAgentBenchmarkData();
//   }, []);

//   return {
//     agentsWithBenchmarks,
//     isLoading,
//     error,
//     refresh: fetchAgentBenchmarkData
//   };
// };