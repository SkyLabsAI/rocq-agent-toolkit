'use client'

import AdminDashboard from "@/features/admindashboard";
import ComparePage from "@/features/compare";
import { BrowserRouter, MemoryRouter, Route, Routes } from "react-router-dom";


export default function Home() {
  return (
   <MemoryRouter initialEntries={['/']}>
  <Routes>
    <Route path="/" element={<AdminDashboard />} />
    <Route path="/compare" element={<ComparePage/>} />
  </Routes>
</MemoryRouter>
  );
}
