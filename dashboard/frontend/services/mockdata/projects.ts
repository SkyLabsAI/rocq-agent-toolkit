import type {
    Benchmark,
    TaskSet,
    TaskSetResults,
} from '@/types/types';

import { simulateDelay } from './generators';

/**
 * Mock data for tasksets list
 */
export const getProjectsMock = async (): Promise<TaskSet[]> => {
    await simulateDelay(200, 500);

    const mockTaskSets: TaskSet[] = [
        {
            taskset_id: 'taskset_001',
            name: 'Mathematical Proofs',
            description:
                'A comprehensive collection of mathematical theorem proving tasks',
            created_at: new Date(Date.now() - 60 * 86400000).toISOString(),
        },
        {
            taskset_id: 'taskset_002',
            name: 'Logic Puzzles',
            description: 'Logical reasoning and puzzle solving challenges',
            created_at: new Date(Date.now() - 45 * 86400000).toISOString(),
        },
        {
            taskset_id: 'taskset_003',
            name: 'Formal Verification',
            description: 'Advanced formal verification test suite',
            created_at: new Date(Date.now() - 30 * 86400000).toISOString(),
        },
        {
            taskset_id: 'taskset_004',
            name: 'Code Generation',
            description: 'Automated code generation and synthesis tasks',
            created_at: new Date(Date.now() - 20 * 86400000).toISOString(),
        },
        {
            taskset_id: 'taskset_005',
            name: 'Research Benchmarks',
            description: 'Research-oriented benchmark suite for agent evaluation',
            created_at: new Date(Date.now() - 10 * 86400000).toISOString(),
        },
    ];

    console.log('Fetched tasksets (MOCK):', mockTaskSets);
    return mockTaskSets;
};

/**
 * Mock data for datasets within a taskset
 */
export const getProjectDatasetsMock = async (
    tasksetId: string
): Promise<Benchmark[]> => {
    await simulateDelay(200, 500);

    // Map tasksets to datasets
    const tasksetDatasetsMap: Record<string, Benchmark[]> = {
        taskset_001: [
            {
                dataset_id: 'benchmark_001',
                description: 'Collection of mathematical theorem proving tasks',
                created_at: new Date(Date.now() - 30 * 86400000).toISOString(),
            },
            {
                dataset_id: 'benchmark_002',
                description: 'Advanced algebra and geometry proofs',
                created_at: new Date(Date.now() - 25 * 86400000).toISOString(),
            },
        ],
        taskset_002: [
            {
                dataset_id: 'benchmark_003',
                description: 'Logical reasoning and puzzle solving challenges',
                created_at: new Date(Date.now() - 15 * 86400000).toISOString(),
            },
        ],
        taskset_003: [
            {
                dataset_id: 'benchmark_004',
                description: 'Advanced formal verification test suite',
                created_at: new Date(Date.now() - 7 * 86400000).toISOString(),
            },
            {
                dataset_id: 'benchmark_005',
                description: 'Software verification benchmarks',
                created_at: new Date(Date.now() - 5 * 86400000).toISOString(),
            },
        ],
        taskset_004: [
            {
                dataset_id: 'benchmark_006',
                description: 'Code generation tasks',
                created_at: new Date(Date.now() - 12 * 86400000).toISOString(),
            },
        ],
        taskset_005: [
            {
                dataset_id: 'benchmark_007',
                description: 'Research-oriented benchmark suite',
                created_at: new Date(Date.now() - 8 * 86400000).toISOString(),
            },
            {
                dataset_id: 'benchmark_008',
                description: 'Agent evaluation metrics',
                created_at: new Date(Date.now() - 3 * 86400000).toISOString(),
            },
        ],
    };

    const datasets = tasksetDatasetsMap[tasksetId] || [];

    console.log(`Fetched datasets for taskset ${tasksetId} (MOCK):`, datasets);
    return datasets;
};

/**
 * Mock data for taskset results (tasks vs agent instances matrix)
 */
export const getProjectResultsMock = async (
    tasksetId: string
): Promise<TaskSetResults> => {
    await simulateDelay(300, 600);

    // Generate tasks for each taskset
    const tasksPerTaskSet: Record<string, number> = {
        taskset_001: 15,
        taskset_002: 10,
        taskset_003: 20,
        taskset_004: 12,
        taskset_005: 18,
    };

    // Generate agent instances for each taskset
    const agentInstancesPerTaskSet: Record<
        string,
        Array<{ name: string; checksum: string }>
    > = {
        taskset_001: [
            { name: 'ProofBot-v2.1', checksum: 'checksum_001' },
            { name: 'MathSolver-Alpha', checksum: 'checksum_002' },
            { name: 'TheoremProver', checksum: 'checksum_003' },
            { name: 'LogicMaster', checksum: 'checksum_004' },
        ],
        taskset_002: [
            { name: 'PuzzleSolver', checksum: 'checksum_005' },
            { name: 'LogicBot', checksum: 'checksum_006' },
            { name: 'ReasoningAgent', checksum: 'checksum_007' },
        ],
        taskset_003: [
            { name: 'Verifier-Pro', checksum: 'checksum_008' },
            { name: 'FormalCheck', checksum: 'checksum_009' },
            { name: 'SafetyValidator', checksum: 'checksum_010' },
            { name: 'CorrectnessProver', checksum: 'checksum_011' },
            { name: 'BugHunter', checksum: 'checksum_012' },
        ],
        taskset_004: [
            { name: 'CodeGen-Alpha', checksum: 'checksum_013' },
            { name: 'Synthesizer', checksum: 'checksum_014' },
            { name: 'AutoCoder', checksum: 'checksum_015' },
        ],
        taskset_005: [
            { name: 'ResearchBot', checksum: 'checksum_016' },
            { name: 'BenchmarkRunner', checksum: 'checksum_017' },
            { name: 'Evaluator', checksum: 'checksum_018' },
            { name: 'MetricsCollector', checksum: 'checksum_019' },
        ],
    };

    const numTasks = tasksPerTaskSet[tasksetId] || 10;
    const agentInstances = agentInstancesPerTaskSet[tasksetId] || [
        { name: 'DefaultAgent', checksum: 'checksum_default' },
    ];

    // Generate tasks with dynamic tags (simulating API data)
    // Tags are generated based on task index to create variety
    const categories = ['algebra', 'geometry', 'logic', 'proof', 'verification'];
    const priorities = ['high', 'medium', 'low'];
    const difficulties = ['easy', 'medium', 'hard'];
    const statuses = ['active', 'pending', 'completed'];

    const tasks = Array.from({ length: numTasks }, (_, i) => {
        // Generate tags dynamically - some tasks have tags, some don't
        const tags: Record<string, string> = {};

        // 70% of tasks have tags
        if (Math.random() > 0.3) {
            // Randomly assign 1-3 tags per task
            const numTags = Math.floor(Math.random() * 3) + 1;

            if (numTags >= 1) {
                tags.category = categories[i % categories.length];
            }
            if (numTags >= 2 && Math.random() > 0.5) {
                tags.priority = priorities[i % priorities.length];
            }
            if (numTags >= 3 && Math.random() > 0.5) {
                tags.difficulty = difficulties[i % difficulties.length];
            }
            if (Math.random() > 0.7) {
                tags.status = statuses[i % statuses.length];
            }
        }

        return {
            task_id: `task_${tasksetId}_${(i + 1).toString().padStart(3, '0')}`,
            task_kind: 'FullProofTask' as const,
            dataset_id: `benchmark_${String((i % 3) + 1).padStart(3, '0')}`,
            tags: Object.keys(tags).length > 0 ? tags : undefined,
        };
    });

    // Generate agent instances with run IDs
    const instances = agentInstances.map(agent => ({
        agent_instance_id: `instance_${tasksetId}_${agent.checksum}`,
        agent_name: agent.name,
        agent_checksum: agent.checksum,
        run_id: `run_${tasksetId}_${agent.checksum}_001`,
    }));

    // Generate results matrix (each agent instance runs each task)
    // Each result contains counts of successful runs and total runs
    const results: Array<{
        task_id: string;
        agent_instance_id: string;
        success_count: number;
        total_count: number;
    }> = [];

    tasks.forEach(task => {
        instances.forEach(instance => {
            // Generate run counts with some randomness but deterministic per combination
            const seed = `${task.task_id}_${instance.agent_instance_id}`;
            const hash = seed.split('').reduce((acc, char) => {
                return ((acc << 5) - acc + char.charCodeAt(0)) | 0;
            }, 0);

            // Generate total runs (0-8, with ~80% chance of having at least 1 run)
            const totalCount =
                Math.abs(hash) % 10 === 0 ? 0 : (Math.abs(hash) % 8) + 1;

            // Generate success count (0 to total_count, with ~60-70% success rate)
            let successCount = 0;
            if (totalCount > 0) {
                const successRate = (Math.abs(hash) % 3) + 5; // 5-7 out of 10 = 50-70%
                successCount = Math.floor((totalCount * successRate) / 10);
                // Ensure at least some variation
                if (successCount === totalCount && totalCount > 1) {
                    successCount = totalCount - 1;
                }
            }

            results.push({
                task_id: task.task_id,
                agent_instance_id: instance.agent_instance_id,
                success_count: successCount,
                total_count: totalCount,
            });
        });
    });

    const tasksetResults: TaskSetResults = {
        taskset_id: tasksetId,
        tasks,
        agent_instances: instances,
        results,
    };

    console.log(
        `Fetched results for taskset ${tasksetId} (MOCK):`,
        tasksetResults
    );
    return tasksetResults;
};
