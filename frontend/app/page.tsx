'use client'

import AgentCompareTable from "@/features/agents-compare";
import LocalDashboard from "@/features/localdashboard";
import ComparePage from "@/features/runs-compare";

import { BrowserRouter, MemoryRouter, Route, Routes } from "react-router-dom";


export default function Home() {
  return (
   <MemoryRouter initialEntries={['/']}>
  <Routes>
    <Route path="/" element={<LocalDashboard />} />
    <Route path="/compare/agents" element={<AgentCompareTable/>} />
    <Route path="/compare" element={<ComparePage/>} />

    <Route path="*" element={<div>404 Not Found</div>} />
  </Routes>
</MemoryRouter>
  );
}
