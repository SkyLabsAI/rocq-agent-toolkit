import { act, renderHook } from '@testing-library/react';
import React from 'react';

import { type Run } from '@/types/types';

import { SelectedRunProvider, useSelectedRun } from './selected-run-context';

describe('SelectedRunContext', () => {
  const mockRun: Run = {
    run_id: 'run-1',
    agent_name: 'test-agent',
    timestamp_utc: '2024-01-01T00:00:00Z',
    total_tasks: 10,
    success_count: 8,
    failure_count: 2,
    dataset_id: 'dataset-1',
    metadata: { tags: {} },
  };

  const wrapper = ({ children }: { children: React.ReactNode }) => (
    <SelectedRunProvider>{children}</SelectedRunProvider>
  );

  describe('useSelectedRun hook', () => {
    it('should throw error when used outside provider', () => {
      const consoleError = jest.spyOn(console, 'error').mockImplementation();

      expect(() => {
        renderHook(() => useSelectedRun());
      }).toThrow('useSelectedRun must be used within a SelectedRunProvider');

      consoleError.mockRestore();
    });

    it('should initialize with null selected run', () => {
      const { result } = renderHook(() => useSelectedRun(), { wrapper });

      expect(result.current.selectedRun).toBeNull();
    });
  });

  describe('Run selection', () => {
    it('should set selected run', () => {
      const { result } = renderHook(() => useSelectedRun(), { wrapper });

      act(() => {
        result.current.setSelectedRun(mockRun);
      });

      expect(result.current.selectedRun).toEqual(mockRun);
    });

    it('should clear selected run when set to null', () => {
      const { result } = renderHook(() => useSelectedRun(), { wrapper });

      act(() => {
        result.current.setSelectedRun(mockRun);
      });

      expect(result.current.selectedRun).toEqual(mockRun);

      act(() => {
        result.current.setSelectedRun(null);
      });

      expect(result.current.selectedRun).toBeNull();
    });

    it('should update selected run when changed', () => {
      const { result } = renderHook(() => useSelectedRun(), { wrapper });

      const anotherRun: Run = {
        run_id: 'run-2',
        agent_name: 'another-agent',
        timestamp_utc: '2024-01-02T00:00:00Z',
        total_tasks: 15,
        success_count: 12,
        failure_count: 3,
        dataset_id: 'dataset-2',
        metadata: { tags: {} },
      };

      act(() => {
        result.current.setSelectedRun(mockRun);
      });

      expect(result.current.selectedRun).toEqual(mockRun);

      act(() => {
        result.current.setSelectedRun(anotherRun);
      });

      expect(result.current.selectedRun).toEqual(anotherRun);
    });
  });
});
