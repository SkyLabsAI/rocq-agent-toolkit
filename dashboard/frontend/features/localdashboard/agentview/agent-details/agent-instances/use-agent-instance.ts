import { useState } from 'react';

export const useAgentInstance = (instanceChecksum: string) => {
  const [isLoading] = useState(false);

  // This hook can be expanded in the future to fetch instance-specific data
  // For now, we'll use the benchmarks passed from parent

  return {
    isLoading,
    instanceChecksum,
  };
};
