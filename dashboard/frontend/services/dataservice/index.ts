import { AgentRun, AgentSummary, RunDetailsResponse } from "@/types/types"
import axios from "axios"
import { config } from "@/config/env"

export const getData: () => Promise<AgentSummary[]> = async () => {
    const response = await axios.get(`${config.DATA_API}/agents`)
    console.log("Fetched agent summaries:", response.data)
    return response.data as Promise<AgentSummary[]>
}




export const getDetails = async (agentName: string): Promise<AgentRun[]> => {
    const response = await axios.get(`${config.DATA_API}/agents/${agentName}/runs`)
    console.log("Fetched agent runs:", response.data)
    return response.data as Promise<AgentRun[]>
}

export const getRunDetails = async (runIds: string[]): Promise<RunDetailsResponse[]> => {
    const runIdsParam = runIds.join(',');
    const response = await axios.get(`${config.DATA_API}/runs/details?run_ids=${runIdsParam}`)
    console.log("Fetched run details:", response.data)
    return response.data as RunDetailsResponse[];
}

export const getObservabilityLogs = async (runId: string, taskId: string): Promise<Record<string, unknown>> => {
    const encodedTaskId = encodeURIComponent(taskId);
    const response = await axios.get(`${config.DATA_API}/observability/logs?run_id=${runId}&task_id=${encodedTaskId}`)
    console.log("Fetched observability logs:", response.data)
    return response.data.labels || {};
}

export const refreshData = async (): Promise<{ success: boolean; message: string; total_tasks: number; total_agents: number }> => {
    const response = await axios.post(`${config.DATA_API}/refresh`)
    console.log("Refresh response:", response.data)
    return response.data
}

// export const getRunData = async (runId: string): Promise<TaskOutput[]> => {
//     for (const agent of AgentData) {
//         for (const run of agent.runs) {
//             if (run.id === runId) {
//                 return run.data
//             }
//         }
//     }
//     throw new Error("Run not found")
// }