'use client';

import Link from 'next/link';
import React, { useEffect, useState } from 'react';

import { TagsDisplay } from '@/components/tags-display';
import { config } from '@/config/environment';
import { getLatestRuns } from '@/services/dataservice';
import { type AgentRun } from '@/types/types';

const LatestRunsList: React.FC = () => {
  const [runs, setRuns] = useState<AgentRun[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    const fetchLatestRuns = async () => {
      try {
        setLoading(true);
        setError(null);
        const data = await getLatestRuns(config.LATEST_RUNS_LIMIT);
        setRuns(data);
      } catch (err) {
        console.error('Failed to fetch latest runs:', err);
        setError('Failed to load latest runs');
      } finally {
        setLoading(false);
      }
    };

    fetchLatestRuns();
  }, []);

  if (loading) {
    return (
      <div className='backdrop-blur-sm border bg-elevation-surface border-elevation-surface-raised rounded-xl overflow-hidden mb-6'>
        <div className='px-6 py-4 border-b border-elevation-surface-raised bg-elevation-surface-raised'>
          <h2 className='text-[18px] font-semibold text-text leading-6'>
            Latest Runs
          </h2>
        </div>
        <div className='px-6 py-8 text-center text-text-subtlest'>
          Loading...
        </div>
      </div>
    );
  }

  if (error) {
    return (
      <div className='backdrop-blur-sm border bg-elevation-surface border-elevation-surface-raised rounded-xl overflow-hidden mb-6'>
        <div className='px-6 py-4 border-b border-elevation-surface-raised bg-elevation-surface-raised'>
          <h2 className='text-[18px] font-semibold text-text leading-6'>
            Latest Runs
          </h2>
        </div>
        <div className='px-6 py-8 text-center text-red-500'>{error}</div>
      </div>
    );
  }

  if (runs.length === 0) {
    return (
      <div className='backdrop-blur-sm border bg-elevation-surface border-elevation-surface-raised rounded-xl overflow-hidden mb-6'>
        <div className='px-6 py-4 border-b border-elevation-surface-raised bg-elevation-surface-raised'>
          <h2 className='text-[18px] font-semibold text-text leading-6'>
            Latest Runs
          </h2>
        </div>
        <div className='px-6 py-8 text-center text-text-subtlest'>
          No runs found
        </div>
      </div>
    );
  }

  const formatTimestamp = (timestamp: string) => {
    const date = new Date(timestamp);
    return date.toLocaleString('en-US', {
      month: 'short',
      day: 'numeric',
      hour: '2-digit',
      minute: '2-digit',
    });
  };

  const getSuccessRate = (run: AgentRun) => {
    if (run.total_tasks === 0) return 0;
    return ((run.success_count / run.total_tasks) * 100).toFixed(1);
  };

  return (
    <div className='backdrop-blur-sm border bg-elevation-surface border-elevation-surface-raised rounded-xl overflow-hidden mb-6'>
      <div className='px-6 py-4 border-b border-elevation-surface-raised bg-elevation-surface-raised'>
        <h2 className='text-[18px] font-semibold text-text leading-6'>
          Latest Runs
        </h2>
        <p className='text-text-subtlest text-[14px] mt-1 leading-5'>
          Most recent agent runs across all datasets
        </p>
      </div>
      <div className='overflow-x-auto'>
        <table className='w-full'>
          <thead className='bg-elevation-surface-raised'>
            <tr className='text-left text-text-subtlest text-[13px] font-medium'>
              <th className='px-6 py-3'>Run ID</th>
              <th className='px-6 py-3'>Agent Name</th>
              <th className='px-6 py-3'>Dataset</th>
              <th className='px-6 py-3'>Timestamp</th>
              <th className='px-6 py-3 text-center'>Tasks</th>
              <th className='px-6 py-3 text-center'>Success Rate</th>
              <th className='px-6 py-3'>Tags</th>
            </tr>
          </thead>
          <tbody className='divide-y divide-elevation-surface-raised'>
            {runs.map((run, index) => (
              <tr
                key={run.run_id}
                className='hover:bg-elevation-surface-raised transition-colors'
              >
                <td className='px-6 py-4'>
                  <Link
                    href={`/runs/${run.run_id}`}
                    className='text-text-link hover:underline font-mono text-[13px]'
                  >
                    {run.run_id.slice(0, 8)}...
                  </Link>
                </td>
                <td className='px-6 py-4 text-text text-[14px]'>
                  {run.agent_name}
                </td>
                <td className='px-6 py-4 text-text-subtlest text-[13px]'>
                  {run.dataset_id || '-'}
                </td>
                <td className='px-6 py-4 text-text-subtlest text-[13px]'>
                  {formatTimestamp(run.timestamp_utc)}
                </td>
                <td className='px-6 py-4 text-center text-text text-[14px]'>
                  <span className='inline-flex items-center gap-1'>
                    <span className='text-green-500'>{run.success_count}</span>
                    <span className='text-text-subtlest'>/</span>
                    <span>{run.total_tasks}</span>
                  </span>
                </td>
                <td className='px-6 py-4 text-center'>
                  <span
                    className={`inline-flex items-center px-2.5 py-0.5 rounded-full text-xs font-medium ${
                      parseFloat(getSuccessRate(run)) >= 80
                        ? 'bg-green-100 text-green-800 dark:bg-green-900 dark:text-green-200'
                        : parseFloat(getSuccessRate(run)) >= 50
                          ? 'bg-yellow-100 text-yellow-800 dark:bg-yellow-900 dark:text-yellow-200'
                          : 'bg-red-100 text-red-800 dark:bg-red-900 dark:text-red-200'
                    }`}
                  >
                    {getSuccessRate(run)}%
                  </span>
                </td>
                <td className='px-6 py-4'>
                  {run.metadata?.tags &&
                  Object.keys(run.metadata.tags).length > 0 ? (
                    <TagsDisplay
                      tags={run.metadata.tags}
                      maxVisible={2}
                      modalTitle={`All Tags for ${run.run_id}`}
                    />
                  ) : (
                    <span className='text-text-subtlest text-[13px]'>-</span>
                  )}
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </div>
  );
};

export default LatestRunsList;
