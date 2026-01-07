import AgentCompareTable from '@/features/agents-compare';

interface CompareAgentsPageProps {
  searchParams: Promise<{ agents?: string }>;
}

const CompareAgents = async ({ searchParams }: CompareAgentsPageProps) => {
  const params = await searchParams;
  const agents = params.agents || '';
  const agentIds = agents
    .split(',')
    .map(name => name.trim())
    .filter(Boolean);

  return <AgentCompareTable agentIds={agentIds} />;
};

export default CompareAgents;
