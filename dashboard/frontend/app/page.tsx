'use client'

import LocalDashboard from "@/features/localdashboard";
import ComparePage from "@/features/compare";
import { BrowserRouter, MemoryRouter, Route, Routes } from "react-router-dom";


export default function Home() {
  return (
   <MemoryRouter initialEntries={['/']}>
  <Routes>
    <Route path="/" element={<LocalDashboard />} />
    <Route path="/compare" element={<ComparePage/>} />
  </Routes>
</MemoryRouter>
  );
}
