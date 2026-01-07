import { useEffect, useState } from 'react';

import { getTaskSets, getProjects } from '@/services/dataservice';
import { type TaskSet } from '@/types/types';

export const useTaskSets = () => {
    const [tasksets, setTaskSets] = useState<TaskSet[]>([]);
    const [loading, setLoading] = useState<boolean>(true);
    const [error, setError] = useState<string | null>(null);

    const fetchTaskSets = async () => {
        try {
            setLoading(true);
            setError(null);
            const data = await getTaskSets();
            setTaskSets(data);
        } catch (err) {
            setError(
                err instanceof Error ? err.message : 'Failed to fetch tasksets'
            );
        } finally {
            setLoading(false);
        }
    };

    useEffect(() => {
        fetchTaskSets();
    }, []);

    return {
        tasksets,
        loading,
        error,
        refetch: fetchTaskSets,
    };
};

// Legacy export for backward compatibility
export const useProjects = useTaskSets;

