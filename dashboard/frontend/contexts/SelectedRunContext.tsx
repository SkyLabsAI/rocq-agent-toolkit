import React, { createContext, useContext, useState, ReactNode } from "react";


export interface Run {
  run_id: string;
  agent_name: string;
  timestamp_utc: string;
  total_tasks: number;
  success_count: number;
  failure_count: number;
}

interface SelectedRunContextType {
  selectedRun: Run | null;
  setSelectedRun: (run: Run | null) => void;
}

const SelectedRunContext = createContext<SelectedRunContextType | undefined>(undefined);

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
    throw new Error("useSelectedRun must be used within a SelectedRunProvider");
  }
  return context;
};
