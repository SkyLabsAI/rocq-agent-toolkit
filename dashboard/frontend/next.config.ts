import type { NextConfig } from "next";

const isStaticBuild = process.env.BUILD_STATIC === 'true';

const nextConfig: NextConfig = {
  /* config options here */
  ...(isStaticBuild && { output: 'export' }),
  ...(!isStaticBuild && { output: 'standalone' }),
};

export default nextConfig;
