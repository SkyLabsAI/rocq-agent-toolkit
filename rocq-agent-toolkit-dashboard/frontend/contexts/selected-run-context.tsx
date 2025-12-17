'use client';
import { createContext, type ReactNode, useContext, useState } from 'react';

import { type Run } from '@/types/types';

interface SelectedRunContextType {
  selectedRun: Run | null;
  setSelectedRun: (run: Run | null) => void;
}

const SelectedRunContext = createContext<SelectedRunContextType | undefined>(
  undefined
);

export const SelectedRunProvider = ({ children }: { children: ReactNode }) => {
  const [selectedRun, setSelectedRun] = useState<Run | null>(null);

  return (
    <SelectedRunContext.Provider value={{ selectedRun, setSelectedRun }}>
      {children}
    </SelectedRunContext.Provider>
  );
};

export const useSelectedRun = () => {
  const context = useContext(SelectedRunContext);
  if (!context) {
    throw new Error('useSelectedRun must be used within a SelectedRunProvider');
  }
  return context;
};
