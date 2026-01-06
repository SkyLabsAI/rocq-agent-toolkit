import ComparePage from '@/features/runs-compare';

interface ComparePageProps {
  searchParams: Promise<{ runs?: string }>;
}

const Compare = async ({ searchParams }: ComparePageProps) => {
  const params = await searchParams;
  const runs = params.runs || '';
  const runIds = runs
    .split(',')
    .map(r => r.trim())
    .filter(Boolean);

  return <ComparePage runIds={runIds} />;
};

export default Compare;
