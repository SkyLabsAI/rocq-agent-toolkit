'use client';

import { MemoryRouter, Route, Routes } from 'react-router-dom';

import AgentCompareTable from '@/features/agents-compare';
import LocalDashboard from '@/features/dashboard';
import ComparePage from '@/features/runs-compare';

const Home = () => {
  return (
    <MemoryRouter initialEntries={['/']}>
      <Routes>
        <Route path='/' element={<LocalDashboard />} />
        <Route path='/agents' element={<LocalDashboard />} />
        <Route path='/compare/agents' element={<AgentCompareTable />} />
        <Route path='/compare' element={<ComparePage />} />

        <Route path='*' element={<div>404 Not Found</div>} />
      </Routes>
    </MemoryRouter>
  );
};

export default Home;
