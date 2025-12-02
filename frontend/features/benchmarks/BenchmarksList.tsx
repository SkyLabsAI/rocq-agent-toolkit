'use client';

import React, { useEffect, useState } from 'react';
import { useNavigate } from 'react-router-dom';
import Layout from '@/layouts/common';
import { getBenchmarks } from '@/services/dataservice';
import { Benchmark } from '@/types/types';
import Button from '@/components/base/ui/button';
import { RefreshIcon } from '@/icons/refresh';

const BenchmarksList: React.FC = () => {
  const [benchmarks, setBenchmarks] = useState<Benchmark[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const navigate = useNavigate();

  const loadBenchmarks = async () => {
    try {
      setLoading(true);
      setError(null);
      const data = await getBenchmarks();
      setBenchmarks(data);
    } catch (err) {
      console.error('Error loading benchmarks:', err);
      setError('Failed to load benchmarks');
    } finally {
      setLoading(false);
    }
  };

  useEffect(() => {
    loadBenchmarks();
  }, []);

  const handleBenchmarkClick = (benchmark: Benchmark) => {
    // Navigate to agents page with benchmark filter
    navigate(`/agents?benchmark=${benchmark.dataset_id}`);
  };

  return (
    <Layout title="Benchmarks">
      <div className="backdrop-blur-sm border bg-elevation-surface border-elevation-surface-raised rounded-xl overflow-hidden">
        <div className="px-6 py-4 border-b border-elevation-surface-raised flex items-center justify-between bg-elevation-surface-raised">
          <div>
            <h2 className="text-[18px] font-semibold text-text leading-6">
              Available Benchmarks
            </h2>
            <p className="text-text-subtlest text-[14px] mt-1 leading-5">
              Select a benchmark to view agent performance
            </p>
          </div>

          <div className="items-center flex gap-2">
            <Button
              onClick={loadBenchmarks}
              disabled={loading}
              variant="default"
              leftIcon={
                !loading ? (
                  <RefreshIcon className="h-5 w-5" />
                ) : undefined
              }
            >
              {loading ? 'Loading...' : 'Refresh'}
            </Button>
          </div>
        </div>

        <div className="p-6">
          {error && (
            <div className="mb-4 bg-red-500/10 border border-red-500/20 rounded-lg p-4">
              <p className="text-sm text-red-400">{error}</p>
            </div>
          )}

          {loading ? (
            <div className="text-center py-12">
              <p className="text-text-disabled">Loading benchmarks...</p>
            </div>
          ) : benchmarks.length === 0 ? (
            <div className="text-center py-12">
              <p className="text-text-disabled">No benchmarks available</p>
            </div>
          ) : (
            <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
              {benchmarks.map((benchmark) => (
                <button
                  key={benchmark.dataset_id}
                  onClick={() => handleBenchmarkClick(benchmark)}
                  className="group relative bg-elevation-surface-raised border border-elevation-surface-overlay hover:border-primary-default transition-all duration-200 rounded-lg p-6 text-left cursor-pointer hover:shadow-lg hover:shadow-primary-default/10"
                >
                  <div className="flex flex-col gap-2">
                    <h3 className="text-[16px] font-semibold text-text group-hover:text-primary-default transition-colors">
                      {benchmark.dataset_id}
                    </h3>
                    <p className="text-[14px] text-text-subtlest">
                      ID: {benchmark.dataset_id}
                    </p>
                  </div>
                  <div className="absolute top-4 right-4 opacity-0 group-hover:opacity-100 transition-opacity">
                    <svg
                      className="w-5 h-5 text-primary-default"
                      fill="none"
                      stroke="currentColor"
                      viewBox="0 0 24 24"
                    >
                      <path
                        strokeLinecap="round"
                        strokeLinejoin="round"
                        strokeWidth={2}
                        d="M9 5l7 7-7 7"
                      />
                    </svg>
                  </div>
                </button>
              ))}
            </div>
          )}
        </div>
      </div>
    </Layout>
  );
};

export default BenchmarksList;
