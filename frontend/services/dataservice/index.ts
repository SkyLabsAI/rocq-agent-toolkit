import { AgentRun, AgentSummary, RunDetailsResponse, TaskOutput } from "@/types/types"
import axios from "axios"
import { config } from "@/config/env"

// Check if we should use mock data
const USE_MOCK_DATA = process.env.NEXT_PUBLIC_USE_MOCK_DATA === 'true';

// Mock data generator functions
const generateMockTaskOutput = (runId: string, agentName: string, taskIndex: number): TaskOutput => {
    const isSuccess = Math.random() > 0.3; // 70% success rate
    const taskId = `task_${taskIndex.toString().padStart(3, '0')}`;
    
    return {
        run_id: runId,
        task_kind: "FullProofTask",
        task_id: taskId,
        trace_id: `trace_${Math.random().toString(36).substring(2, 15)}`,
        timestamp_utc: new Date(Date.now() - Math.random() * 86400000).toISOString(),
        agent_name: agentName,
        status: isSuccess ? "Success" : "Failure",
        failure_reason: !isSuccess ? [
            "Proof step failed during execution",
            "Timeout exceeded after 30 seconds",
            "Unable to find valid tactic sequence"
        ] : undefined,
        results: {
            proof_found: isSuccess,
            steps_taken: Math.floor(Math.random() * 50) + 1
        },
        metrics: {
            llm_invocation_count: Math.floor(Math.random() * 20) + 5,
            token_counts: {
                input_tokens: Math.floor(Math.random() * 5000) + 1000,
                output_tokens: Math.floor(Math.random() * 2000) + 500,
                total_tokens: 0
            },
            resource_usage: {
                execution_time_sec: Math.random() * 30 + 5,
                cpu_time_sec: Math.random() * 25 + 3,
                gpu_time_sec: Math.random() * 10 + 1
            },
            custom: null,
            custom_metrics: {
                proof_complexity: Math.floor(Math.random() * 10) + 1
            },
            timestamp: new Date().toISOString()
        }
    };
};

// Real API functions
const getDataReal: () => Promise<AgentSummary[]> = async () => {
    const response = await axios.get(`${config.DATA_API}/agents`)
    console.log("Fetched agent summaries:", response.data)
    return response.data as AgentSummary[]
}

// Mock API functions
const getDataMock: () => Promise<AgentSummary[]> = async () => {
    await new Promise(resolve => setTimeout(resolve, 500)); // Simulate network delay
    
    const mockData: AgentSummary[] = [
        { agent_name: "RocqAgent_v1", total_runs: 15 },
        { agent_name: "ProofAssistant_v2", total_runs: 12 },
        { agent_name: "TacticExplorer_v3", total_runs: 8 },
        { agent_name: "CoqHelper_v1", total_runs: 20 }
    ];
    
    console.log("Fetched agent summaries (MOCK):", mockData);
    return mockData;
}

export const getData = USE_MOCK_DATA ? getDataMock : getDataReal;

const getDetailsReal = async (agentName: string): Promise<AgentRun[]> => {
    const response = await axios.get(`${config.DATA_API}/agents/${agentName}/runs`)
    console.log("Fetched agent runs:", response.data)
    return response.data as AgentRun[]
}

const getDetailsMock = async (agentName: string): Promise<AgentRun[]> => {
    await new Promise(resolve => setTimeout(resolve, 300));
    
    const numRuns = Math.floor(Math.random() * 10) + 5; // 5-15 runs
    const mockRuns: AgentRun[] = [];
    
    for (let i = 0; i < numRuns; i++) {
        const totalTasks = Math.floor(Math.random() * 50) + 20; // 20-70 tasks
        const successCount = Math.floor(totalTasks * (0.6 + Math.random() * 0.3)); // 60-90% success
        
        mockRuns.push({
            run_id: `run_${agentName}_${i.toString().padStart(3, '0')}`,
            agent_name: agentName,
            timestamp_utc: new Date(Date.now() - Math.random() * 7 * 86400000).toISOString(), // Last 7 days
            total_tasks: totalTasks,
            success_count: successCount,
            failure_count: totalTasks - successCount
        });
    }
    
    console.log("Fetched agent runs (MOCK):", mockRuns);
    return mockRuns;
}

export const getDetails = USE_MOCK_DATA ? getDetailsMock : getDetailsReal;

const getRunDetailsReal = async (runIds: string[]): Promise<RunDetailsResponse[]> => {
    const runIdsParam = runIds.join(',');
    const response = await axios.get(`${config.DATA_API}/runs/details?run_ids=${runIdsParam}`)
    console.log("Fetched run details:", response.data)
    return response.data as RunDetailsResponse[];
}

const getRunDetailsMock = async (runIds: string[]): Promise<RunDetailsResponse[]> => {
    await new Promise(resolve => setTimeout(resolve, 800));
    
    const mockRunDetails: RunDetailsResponse[] = runIds.map(runId => {
        const agentName = runId.split('_')[1] || "UnknownAgent";
        const totalTasks = Math.floor(Math.random() * 30) + 10; // 10-40 tasks
        const tasks: TaskOutput[] = [];
        
        for (let i = 0; i < totalTasks; i++) {
            tasks.push(generateMockTaskOutput(runId, agentName, i));
        }
        
        return {
            run_id: runId,
            agent_name: agentName,
            total_tasks: totalTasks,
            tasks
        };
    });
    
    console.log("Fetched run details (MOCK):", mockRunDetails);
    return mockRunDetails;
}

export const getRunDetails = USE_MOCK_DATA ? getRunDetailsMock : getRunDetailsReal;

const getObservabilityLogsReal = async (runId: string, taskId: string): Promise<Record<string, unknown>> => {
    const encodedTaskId = encodeURIComponent(taskId);
    const response = await axios.get(`${config.DATA_API}/observability/logs?run_id=${runId}&task_id=${encodedTaskId}`)
    console.log("Fetched observability logs:", response.data)
    return response.data.labels || {};
}

const getObservabilityLogsMock = async (runId: string, taskId: string): Promise<Record<string, unknown>> => {
    await new Promise(resolve => setTimeout(resolve, 400));
    
    const mockLogs = {
        cpp_code: [
            `// Generated C++ code for ${taskId}\n#include <iostream>\n\nint main() {\n    std::cout << "Hello from ${taskId}" << std::endl;\n    return 0;\n}`,
            `// Alternative implementation\n#include <vector>\n#include <algorithm>\n\nclass Solution {\npublic:\n    void solve() {\n        // Implementation here\n    }\n};`
        ],
        targetContent: [
            `Target theorem for ${taskId}:\nforall n : nat, n + 0 = n.`,
            `Additional target:\nforall x y : nat, x + y = y + x.`
        ],
        lemmaContent: [
            `Lemma helper_${taskId.replace('_', '')} : forall n, S n = n + 1.\nProof.\n  induction n.\n  - reflexivity.\n  - simpl. rewrite IHn. reflexivity.\nQed.`
        ],
        statesContent: [
            `Initial state: Goal (forall n, n + 0 = n)\nTactic applied: induction n\nSubgoal 1: 0 + 0 = 0\nSubgoal 2: forall n, n + 0 = n -> S n + 0 = S n`
        ],
        tactic_info: [
            {
                name: "induction",
                next_tactic_prediction: "induction n.",
                status: "success" as const,
                explaination: "Apply mathematical induction on the variable n to break down the proof into base case and inductive step",
                complexity_score: 7,
                confidence: 0.89,
                execution_time_ms: 145
            },
            {
                name: "reflexivity",
                next_tactic_prediction: "reflexivity.",
                status: "success" as const,
                explaination: "Use reflexivity to prove that 0 + 0 = 0, which is true by definition",
                complexity_score: 2,
                confidence: 0.98,
                execution_time_ms: 23
            },
            {
                name: "simpl_rewrite",
                next_tactic_prediction: "simpl. rewrite IHn. reflexivity.",
                status: "failure" as const,
                explaination: "Attempt to simplify and rewrite using inductive hypothesis, but failed due to context mismatch",
                complexity_score: 5,
                confidence: 0.65,
                execution_time_ms: 98,
                error_message: "Unable to apply rewrite rule in current context"
            },
            {
                name: "auto",
                next_tactic_prediction: "auto.",
                status: "success" as const,
                explaination: "Automatic solver successfully completes the remaining proof obligations",
                complexity_score: 1,
                confidence: 0.95,
                execution_time_ms: 67,
                fallback_tactics: ["trivial", "omega", "lia"]
            }
        ],
        tactic_prediction_explanation: [
            `Step 1: Analyze the goal structure`,
            `Step 2: Identify induction pattern`,
            `Step 3: Apply induction tactic`,
            `Step 4: Solve base case with reflexivity`,
            `Step 5: Solve inductive step using hypothesis`
        ],
        tactic_prediction_tactic: [
            `induction n.`,
            `- reflexivity.`,
            `- simpl. rewrite IHn. reflexivity.`
        ],
        proof_steps: [
            `1. Start with goal: forall n : nat, n + 0 = n`,
            `2. Apply induction on n`,
            `3. Base case: 0 + 0 = 0 (by definition)`,
            `4. Inductive step: assume n + 0 = n, prove S n + 0 = S n`,
            `5. Simplify S n + 0 to S (n + 0)`,
            `6. Rewrite using inductive hypothesis`,
            `7. QED`
        ],
        execution_log: [
            `[INFO] Starting proof for ${taskId}`,
            `[DEBUG] Parsing goal structure`,
            `[INFO] Applying tactic: induction n`,
            `[DEBUG] Generated subgoals: 2`,
            `[INFO] Solving base case`,
            `[INFO] Solving inductive step`,
            `[SUCCESS] Proof completed`
        ],
        metadata: {
            run_id: runId,
            task_id: taskId,
            generated_at: new Date().toISOString(),
            agent_version: "mock_v1.0"
        }
    };
    
    console.log("Fetched observability logs (MOCK):", mockLogs);
    return mockLogs;
}

export const getObservabilityLogs = USE_MOCK_DATA ? getObservabilityLogsMock : getObservabilityLogsReal;

const refreshDataReal = async (): Promise<{ success: boolean; message: string; total_tasks: number; total_agents: number }> => {
    const response = await axios.post(`${config.DATA_API}/refresh`)
    console.log("Refresh response:", response.data)
    return response.data
}

const refreshDataMock = async (): Promise<{ success: boolean; message: string; total_tasks: number; total_agents: number }> => {
    await new Promise(resolve => setTimeout(resolve, 1000));
    
    const mockRefreshResponse = {
        success: true,
        message: "Mock data refreshed successfully",
        total_tasks: Math.floor(Math.random() * 1000) + 500,
        total_agents: Math.floor(Math.random() * 10) + 5
    };
    
    console.log("Refresh response (MOCK):", mockRefreshResponse);
    return mockRefreshResponse;
}

export const refreshData = USE_MOCK_DATA ? refreshDataMock : refreshDataReal;

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